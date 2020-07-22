# Copyright: see copyright.txt

class Constraint:
    def __init__(self, parent, last_predicate, last_extend_vars, last_extend_queries):
        self.parent = parent # 可能是 None 或 Constraint type
        self.last_predicate = last_predicate # 應該是 Predicate type
        self.last_extend_vars = last_extend_vars
        self.last_extend_queries = last_extend_queries
        self.processed = False # 只是給我們看的，程式流程用不到這個
        self.children = [] # 裝了一堆 Constraint type

    def __eq__(self, other):
        """Two Constraints are equal iff they have the same chain of predicates"""
        return isinstance(other, Constraint) and \
            self.parent is other.parent and \
            self.last_predicate == other.last_predicate

    def get_asserts_and_query(self):
        self.processed = True

        # collect the assertions
        asserts = []
        extend_vars = dict()
        extend_queries = []
        tmp = self.parent
        while tmp.last_predicate is not None: # 目前根據 path_to_constraint 的 constructor 猜測，它負責檢測是不是 root constraint
            asserts.append(tmp.last_predicate)
            extend_vars = {**extend_vars, **tmp.last_extend_vars}
            extend_queries += tmp.last_extend_queries
            tmp = tmp.parent
        extend_vars = {**extend_vars, **self.last_extend_vars}
        extend_queries += self.last_extend_queries
        return asserts, self.last_predicate, extend_vars, extend_queries

    def get_length(self):
        if self.parent is None:
            return 0
        return 1 + self.parent.get_length()

    def find_child(self, predicate):
        for c in self.children:
            if predicate == c.last_predicate:
                return c
        return None

    def add_child(self, predicate, last_extend_vars, last_extend_queries):
        assert (self.find_child(predicate) is None)
        c = Constraint(self, predicate, last_extend_vars, last_extend_queries)
        self.children.append(c)
        return c

    def __str__(self):
        return str(self.last_predicate) + "  (processed: %s, path_len: %d)" % (self.processed, self.get_length())
