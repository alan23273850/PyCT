# Copyright: see copyright.txt

# from abc import ABC

class Concolic: #(ABC):
    @staticmethod
    def _find_engine_in_expression(expression):
        from conbyte.explore import ExplorationEngine
        if isinstance(expression, Concolic):
            return expression.engine
        if isinstance(expression, list):
            for e in expression:
                if isinstance(e, list):
                    if (engine := Concolic._find_engine_in_expression(e)) is not None:
                        return engine
                elif isinstance(e, Concolic) and isinstance(e.engine, ExplorationEngine):
                    # print('EEE', e, e.engine)
                    return e.engine
        return None

# https://stackoverflow.com/questions/16056574/how-does-python-prevent-a-class-from-being-subclassed/16056691#16056691
class MetaFinal(type):
    def __new__(cls, name, bases, classdict):
        for b in bases:
            if isinstance(b, cls):
                raise TypeError(f"type '{b.__name__}' is not an acceptable base type")
        return type.__new__(cls, name, bases, dict(classdict))
