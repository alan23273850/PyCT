import ast, builtins, coverage, functools, inspect, json, logging, multiprocessing, os, pickle, re, signal, subprocess, sys, traceback
from conbyte.path import PathToConstraint
from conbyte.solver import Solver
from conbyte.utils import ConcolicObject, unwrap, get_funcobj_from_modpath_and_funcname

log = logging.getLogger("ct.explore")
sys.setrecursionlimit(1000000) # The original limit is not enough in some special cases.

def label(name, num, prev, proc):
    sys.settrace(None) # for efficiency
    signal.signal(num, prev) # restore the original handler
    proc.kill() # kill the alarm if the label is reached early

def goto(label, signum, frame):
    called_from = frame; lineno = label
    if isinstance(lineno, str):
        with open(called_from.f_code.co_filename) as f:
            for node in ast.walk(ast.parse(f.read())):
                if isinstance(node, ast.Call) \
                    and isinstance(node.func, ast.Name) \
                    and node.func.id == 'label' \
                    and lineno == ast.literal_eval(node.args[0]):
                    lineno = node.lineno
    def hook(frame, event, arg):
        if event == 'line' and frame == called_from:
            frame.f_lineno = lineno
            while frame:
                frame.f_trace = None
                frame = frame.f_back
            return None
        return hook
    while frame:
        frame.f_trace = hook
        frame = frame.f_back
    sys.settrace(hook)

def prepare():
    #################################################################
    # Since the source code in https://github.com/python/cpython/blob/e822e37946f27c09953bb5733acf3b07c2db690f/Modules/socketmodule.c#L6485
    # only accepts "unwrapped" input arguments, we simply do it here.
    #################################################################
    import socket
    _socket_getaddrinfo = socket.getaddrinfo
    def socket_getaddrinfo(*args, **kwargs):
        return _socket_getaddrinfo(*map(unwrap, args), **{k: unwrap(v) for (k, v) in kwargs.items()})
    socket.getaddrinfo = socket_getaddrinfo
    #####################################################################
    # The builtin len(...) function will automatically unwrap our result,
    # so we want to avoid this by doing the following line.
    #####################################################################
    builtins.len = lambda x: x.__len__()

class ExplorationEngine:
    class Exception(metaclass=type('', (type,), {"__repr__": lambda self: '<EXCEPTION>'})): pass # indicate occurrence of Exception during execution
    class Timeout(metaclass=type('', (type,), {"__repr__": lambda self: '<TIMEOUT>'})): pass # indicate timeout after either a concolic or a primitive execution
    class Unpicklable(metaclass=type('', (type,), {"__repr__": lambda self: '<UNPICKLABLE>'})): pass # indicate that an object is unpicklable
    class LazyLoading(metaclass=type('', (type,), {"__repr__": lambda self: '<DEFAULT>'})): pass # lazily loading default values of primitive arguments

    def __init__(self, *, solver='cvc4', timeout=10, safety=0, store=None, verbose=1, logfile=None, statsdir=None):
        self.__init2__(); self.statsdir = statsdir
        if self.statsdir: os.system(f"rm -rf '{statsdir}'"); os.system(f"mkdir -p '{statsdir}'")
        Solver.set_basic_configurations(solver, timeout, safety, store, statsdir)
        ############################################################
        # This section mainly deals with the logging settings.
        log_level = 25 - 5 * verbose
        if logfile:
            logging.basicConfig(filename=logfile, level=log_level,
                                format='%(asctime)s  %(name)s\t%(levelname)s\t %(message)s',
                                datefmt='%m/%d/%Y %I:%M:%S %p')
        elif logfile == '':
            logging.basicConfig(level=logging.CRITICAL+1)
        else:
            logging.basicConfig(level=log_level,# stream=sys.stdout,
                                format='  %(name)s\t%(levelname)s\t %(message)s')
        ############################################################
        # We add our new logging level called "SMTLIB2" to print out
        # messages related to the solving process.
        ############################################################
        logging.SMTLIB2 = (logging.DEBUG + logging.INFO) // 2
        logging.addLevelName(logging.SMTLIB2, "SMTLIB2")
        def smtlib2(self, message, *args, **kwargs): # https://stackoverflow.com/questions/2183233/how-to-add-a-custom-loglevel-to-pythons-logging-facility/13638084#13638084
            if self.isEnabledFor(logging.SMTLIB2): # Yes, logger takes its '*args' as 'args'.
                self._log(logging.SMTLIB2, message, args, **kwargs)
        logging.Logger.smtlib2 = smtlib2

    def __init2__(self):
        self.constraints_to_solve = [] # 指的是還沒、但即將被 solver 解出 model 的 constraint
        self.path = PathToConstraint()
        self.in_out = []
        self.coverage_data = coverage.CoverageData()
        self.coverage_accumulated_missing_lines = {}
        self.var_to_types = {}

    def explore(self, modpath, all_args={}, /, *, root='.', funcname=None, max_iterations=200, timeout=15, deadcode=None, include_exception=False, lib=None):
        self.modpath = modpath; self.funcname = funcname; self.timeout = timeout; self.include_exception = include_exception; self.deadcode = deadcode; self.lib = lib
        if self.funcname is None: self.funcname = self.modpath.split('.')[-1]
        self.__init2__(); self.root = os.path.abspath(root); self.target_file = self.root + '/' + self.modpath.replace('.', '/') + '.py'
        self.single_coverage = self.root.startswith(os.path.abspath(os.path.dirname(os.path.dirname(__file__))))
        if self.single_coverage:
            self.coverage = coverage.Coverage(data_file=None, include=[self.target_file])
        else:
            self.coverage = coverage.Coverage(data_file=None, source=[self.root], omit=['**/__pycache__/**', '**/.venv/**'])
        if self.lib: sys.path.insert(0, os.path.abspath(self.lib))
        sys.path.insert(0, self.root); sys.path.insert(0, os.path.abspath(os.path.dirname(os.path.join(self.root, self.modpath.replace('.', '/') + '.py'))))
        now_dir = os.getcwd(); os.chdir(os.path.abspath(os.path.dirname(os.path.join(self.root, self.modpath.replace('.', '/') + '.py'))))
        prev = signal.signal(num := max(signal.valid_signals()), functools.partial(goto, '1'))
        proc = subprocess.Popen(f"sleep {15*60} && kill -{num} {os.getpid()}", shell=True)
        iterations = 1; cont = self._one_execution(all_args) # the 1st execution
        while cont and iterations < max_iterations and len(self.constraints_to_solve) > 0:
            ##############################################################
            # In each iteration, we take one constraint out of the queue
            # and try to solve for it. After that we'll obtain a model as
            # a list of arguments and continue the next iteration with it.
            constraint = self.constraints_to_solve.pop(0)
            model = Solver.find_model_from_constraint(self, constraint)
            ##############################################################
            if model is not None:
                log.info(f"=== Iterations: {iterations} ==="); iterations += 1
                all_args.update(model) # from model to argument
                cont = self._one_execution(all_args) # other consecutive executions following the 1st execution
        label('1', num, prev, proc); os.chdir(now_dir); del sys.path[0:2]
        if self.lib: del sys.path[0]
        if self.statsdir:
            with open(self.statsdir + '/inputs.pkl', 'wb') as f:
                pickle.dump([e[0] for e in self.in_out], f) # store only inputs
            with open(self.statsdir + '/smt.csv', 'w') as f:
                f.write(',number,time\n')
                f.write(f'sat,{Solver.stats["sat_number"]},{Solver.stats["sat_time"]}\n')
                f.write(f'unsat,{Solver.stats["unsat_number"]},{Solver.stats["unsat_time"]}\n')
                f.write(f'otherwise,{Solver.stats["otherwise_number"]},{Solver.stats["otherwise_time"]}\n')
        return iterations - 1

    def _one_execution(self, all_args):
        result = self._one_execution_concolic(all_args) # primitive input arguments "all_args" may be modified here.
        if self.statsdir: # We don't measure coverage in primitive environments here in the project mode.
            self.in_out.append((all_args.copy(), result)) # .copy() is important! Think why.
            return True # continue iteration
        answer = self._one_execution_primitive(all_args)
        if self.Timeout not in (result, answer):
            if result != answer: print('Input:', all_args, '／My result:', result, '／Correct answer:', answer)
            assert result == answer
        for file in self.coverage_data.measured_files(): # "file" is absolute here.
            if missing_lines := self.coverage_accumulated_missing_lines[file]:
                if not self.single_coverage: return True # continue iteration
                if not (file == self.target_file and self.deadcode == missing_lines):
                    log.info(f"Not Covered Yet: {file} {missing_lines}"); return True # continue iteration
        return False # stop iteration

    def _one_execution_concolic(self, all_args):
        r1, s1 = multiprocessing.Pipe(); r2, s2 = multiprocessing.Pipe(); r3, s3 = multiprocessing.Pipe(); r0, s0 = multiprocessing.Pipe()
        def child_process():
            sys.dont_write_bytecode = True # very important to prevent the later primitive environment from using concolic objects imported here...
            prepare(); self.path.__init__(); log.info("Inputs: " + str(all_args))
            import conbyte.wrapper; execute = get_funcobj_from_modpath_and_funcname(self.modpath, self.funcname)
            ccc_args, ccc_kwargs = self._get_concolic_arguments(execute, all_args) # primitive input arguments "all_args" may be modified here.
            s1.send((all_args, self.var_to_types)); result = self.Timeout
            prev = signal.signal(num := max(signal.valid_signals()), functools.partial(goto, '2'))
            proc = subprocess.Popen(f"sleep {self.timeout} && kill -{num} {os.getpid()}", shell=True)
            try:
                result = conbyte.utils.unwrap(execute(*ccc_args, **ccc_kwargs))
            except Exception as e:
                result = self.Exception
                log.error(f"Exception for: {all_args} >> ./py-conbyte.py -r '{self.root}' '{self.modpath}' -s {self.funcname} {{}} -m 20 --lib '{self.lib}' --include_exception --dump_projstats")#; log.error(e); traceback.print_exc()
                if self.statsdir:
                    with open(self.statsdir + '/exception.txt', 'a') as f:
                        print(f"Exception for: {all_args} >> ./py-conbyte.py -r '{self.root}' '{self.modpath}' -s {self.funcname} {{}} -m 20 --lib '{self.lib}' --include_exception --dump_projstats", file=f); print(e, file=f)
            label('2', num, prev, proc); log.info(f"Return: {result}")
            if result is self.Timeout:
                log.error(f"Timeout (soft) for: {all_args} >> ./py-conbyte.py -r '{self.root}' '{self.modpath}' -s {self.funcname} {{}} -m 20 --lib '{self.lib}' --include_exception --dump_projstats")#; traceback.print_exc()
                if self.statsdir:
                    with open(self.statsdir + '/exception.txt', 'a') as f:
                        print(f"Timeout (soft) for: {all_args} >> ./py-conbyte.py -r '{self.root}' '{self.modpath}' -s {self.funcname} {{}} -m 20 --lib '{self.lib}' --include_exception --dump_projstats", file=f)
            ###################################### Communication Section ######################################
            s0.send(0) # just a notification to the parent process that we're going to send data
            try: s2.send(result)
            except: s2.send(self.Unpicklable)
            try: s3.send((self.constraints_to_solve, self.path))
            except: s3.send(self.Unpicklable) # may fail if they contain some unpicklable objects
        process = multiprocessing.Process(target=child_process); process.start()
        (all_args2, self.var_to_types) = r1.recv(); r1.close(); s1.close(); all_args.clear(); all_args.update(all_args2) # update the parameter directly
        if not r0.poll(self.timeout + 5):
            result = self.Timeout
            log.error(f"Timeout (hard) for: {all_args} >> ./py-conbyte.py -r '{self.root}' '{self.modpath}' -s {self.funcname} {{}} -m 20 --lib '{self.lib}' --include_exception --dump_projstats")
            if self.statsdir:
                with open(self.statsdir + '/exception.txt', 'a') as f:
                    print(f"Timeout (hard) for: {all_args} >> ./py-conbyte.py -r '{self.root}' '{self.modpath}' -s {self.funcname} {{}} -m 20 --lib '{self.lib}' --include_exception --dump_projstats", file=f)
        else:
            result = r2.recv()
            if (t:=r3.recv()) is not self.Unpicklable: (self.constraints_to_solve, self.path) = t
        r2.close(); s2.close(); r3.close(); s3.close(); r0.close(); s0.close()
        if process.is_alive(): process.kill()
        return result

    def _one_execution_primitive(self, all_args):
        r1, s1 = multiprocessing.Pipe(); r2, s2 = multiprocessing.Pipe(); r0, s0 = multiprocessing.Pipe()
        def child_process():
            sys.dont_write_bytecode = True # same reason mentioned in the concolic environment
            self.coverage.start(); execute = get_funcobj_from_modpath_and_funcname(self.modpath, self.funcname)
            pri_args, pri_kwargs = self._complete_primitive_arguments(execute, all_args); answer = self.Timeout
            prev = signal.signal(num := max(signal.valid_signals()), functools.partial(goto, '3'))
            proc = subprocess.Popen(f"sleep {self.timeout} && kill -{num} {os.getpid()}", shell=True)
            try: answer = execute(*pri_args, **pri_kwargs)
            except: answer = self.Exception
            label('3', num, prev, proc); self.coverage.stop(); self.coverage_data.update(self.coverage.get_data())
            for file in self.coverage_data.measured_files(): # "file" is absolute here.
                _, _, missing_lines, _ = self.coverage.analysis(file)
                if file not in self.coverage_accumulated_missing_lines:
                    self.coverage_accumulated_missing_lines[file] = set(missing_lines)
                else:
                    self.coverage_accumulated_missing_lines[file] = self.coverage_accumulated_missing_lines[file].intersection(set(missing_lines))
            ###################################### Communication Section ######################################
            s0.send(0) # just a notification to the parent process that we're going to send data
            try: s1.send(answer)
            except: answer = self.Unpicklable; s1.send(answer)
            if self.include_exception or (answer is not self.Exception):
                s2.send((self.coverage_data, self.coverage_accumulated_missing_lines))
            else:
                s2.send(self.Exception)
        process = multiprocessing.Process(target=child_process); process.start()
        if not r0.poll(self.timeout + 5): answer = self.Timeout
        else:
            answer = r1.recv()
            if (t:=r2.recv()) is not self.Exception: (self.coverage_data, self.coverage_accumulated_missing_lines) = t
        self.in_out.append((all_args.copy(), answer)); r1.close(); s1.close(); r2.close(); s2.close(); r0.close(); s0.close()
        if process.is_alive(): process.kill()
        return answer

    @classmethod
    def _complete_primitive_arguments(cls, func, all_args):
        prim_args = []; prim_kwargs = {}
        for v in inspect.signature(func).parameters.values():
            if v.kind in (inspect.Parameter.VAR_POSITIONAL, inspect.Parameter.VAR_KEYWORD): continue # ignore *args, **kwargs at last
            value = v.default if (t:=all_args[v.name]) is cls.LazyLoading else t
            if v.kind is inspect.Parameter.KEYWORD_ONLY:
                prim_kwargs[v.name] = value
            else: # v.kind in (inspect.Parameter.POSITIONAL_ONLY, inspect.Parameter.POSITIONAL_OR_KEYWORD):
                prim_args.append(value)
        return prim_args, prim_kwargs

    def _get_concolic_arguments(self, func, prim_args):
        ccc_args = []; ccc_kwargs = {}
        for v in inspect.signature(func).parameters.values():
            if v.kind in (inspect.Parameter.VAR_POSITIONAL, inspect.Parameter.VAR_KEYWORD):
                prim_args.pop(v.name, None); continue # do not support *args, **kwargs currently
            if v.name in prim_args:
                value = prim_args[v.name]
            else:
                has_value = False
                if (t:=v.annotation) is not inspect._empty:
                    try: value = t(); has_value = True # may raise TypeError: Cannot instantiate ...
                    except: pass
                if not has_value:
                    if (t:=v.default) is not inspect._empty: value = unwrap(t) # default values may also be wrapped
                    else: value = ''
                prim_args[v.name] = value if type(value) in (bool, float, int, str) else self.LazyLoading
            if type(value) in (bool, float, int, str): value = ConcolicObject(value, v.name, self)
            if v.kind is inspect.Parameter.KEYWORD_ONLY:
                ccc_kwargs[v.name] = value
            else: # v.kind in (inspect.Parameter.POSITIONAL_ONLY, inspect.Parameter.POSITIONAL_OR_KEYWORD):
                ccc_args.append(value)
        if not self.var_to_types: # remain unchanged once determined
            for (k, v) in prim_args.items():
                if type(v) is bool: self.var_to_types[k] = 'Bool'
                elif type(v) is float: self.var_to_types[k] = 'Real'
                elif type(v) is int: self.var_to_types[k] = 'Int'
                elif type(v) is str: self.var_to_types[k] = 'String'
                else: pass # for some default values that cannot be concolic-ized
        return ccc_args, ccc_kwargs

    def coverage_statistics(self):
        total_lines = 0
        executed_lines = 0
        missing_lines = {}
        for file in self.coverage_data.measured_files():
            _, executable_lines, _, _ = self.coverage.analysis(file)
            m_lines = self.coverage_accumulated_missing_lines[file]
            total_lines += len(set(executable_lines))
            executed_lines += len(set(executable_lines)) - len(m_lines) # Do not use "len(set(self.coverage_data.lines(file)))" here!!!
            if m_lines: missing_lines[file] = m_lines
            # print(file, executed_lines, total_lines)
        if self.statsdir:
            with open(self.statsdir + '/coverage.txt', 'w') as f:
                f.write("{}/{} ({:.2%})\n".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0))
        return total_lines, executed_lines, missing_lines

    def print_coverage(self):
        total_lines, executed_lines, missing_lines = self.coverage_statistics()
        print("\nLine coverage {}/{} ({:.2%})".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0))
        if missing_lines and self.single_coverage:
            print("Missing lines:") # only print this info when the scope of coverage is a single file.
            for file, lines in missing_lines.items():
                print(f"  {file}: {sorted(lines)}")
        print("")
