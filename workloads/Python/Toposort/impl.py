class Graph:

    def __init__(self):
        self.nodes = set()
        self.edges = []

    def __len__(self):
        return len(self.nodes)

    def add_node(self, node):
        self.nodes.add(node)

    def add_edge(self, start, end):
        self.edges.append((start, end))

    def neighbors(self, node):
        return [end for start, end in self.edges if start == node]

    def toposort(self):
        in_degree = {node: 0 for node in self.nodes}
        for _, end in self.edges:
            in_degree[end] += 1
        #etna_base assume_connected
        queue = [node for node, degree in in_degree.items() if degree == 0]
        #etna_mutant assume_connected
        #queue = [node for node, degree in in_degree.items() if degree == 0][:1]
        #etna_mutant_end assume_connected
        result = []
        while queue:
            node = queue.pop()
            result.append(node)
            for neighbor in self.neighbors(node):
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    queue.append(neighbor)
        #etna_base reverse_result
        return result


#etna_mutant reverse_result
#        return result[::-1]
#etna_mutant_end reverse_result

    def __str__(self):
        return f"Nodes: {self.nodes}, Edges: {self.edges}"

    def __repr__(self):
        return f"Graph({self.nodes}, {self.edges})"

    def has_cycles(self):

        def visit(node, visited, stack):
            visited.add(node)
            stack.add(node)
            for neighbor in self.neighbors(node):
                if neighbor not in visited:
                    if visit(neighbor, visited, stack):
                        return True
                elif neighbor in stack:
                    return True
            stack.remove(node)
            return False

        visited = set()
        for node in self.nodes:
            if node not in visited:
                if visit(node, visited, set()):
                    return True
        return False
