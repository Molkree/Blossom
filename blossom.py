from __future__ import annotations

import copy
from collections.abc import Generator


# https://en.wikipedia.org/wiki/Blossom_algorithm
def get_maximum_matching(graph: Graph, matching: Matching) -> Matching:
    augmenting_path = get_augmenting_path(graph, matching)
    if augmenting_path:
        return get_maximum_matching(graph, matching.augment(augmenting_path))
    return matching


# https://en.wikipedia.org/wiki/Blossom_algorithm
def get_augmenting_path(graph: Graph, matching: Matching) -> list[int]:
    forest = Forest(matching.get_exposed_vertices())
    graph.unmark_all_edges()
    graph.mark_edges(matching.get_edges())
    v = forest.get_unmarked_even_vertice()
    while v is not None:
        e = graph.get_unmarked_neighboring_edge(v)
        while e:
            _, w = e
            if not forest.does_contain_vertice(w):
                x = matching.get_matched_vertice(w)
                forest.add_edge((v, w))
                forest.add_edge((w, x))
            else:
                if forest.get_distance_to_root(w) % 2 == 0:
                    if forest.get_root(v) != forest.get_root(w):
                        path = forest.get_path_from_root_to(
                            v
                        ) + forest.get_path_to_root_from(w)
                        return path
                    else:
                        blossom = forest.get_blossom(v, w)
                        graph_prime = graph.contract(blossom)
                        matching_prime = matching.contract(blossom)
                        path_prime = get_augmenting_path(graph_prime, matching_prime)
                        path = graph.lift_path(path_prime, blossom)
                        return path
            graph.mark_edge(e)
            e = graph.get_unmarked_neighboring_edge(v)
        forest.mark_vertice(v)
        v = forest.get_unmarked_even_vertice()
    return []


class Graph:
    def __init__(self) -> None:
        self.adjacency = dict[int, set[int]]()
        self.unmarked_adjacency = dict[int, set[int]]()
        self.__assert_representation()

    def __assert_representation(self) -> None:
        for t in self.adjacency:
            assert (
                len(self.adjacency[t]) > 0
            ), "If vertice exists in adjacency matrix, it must have at least one neighbor"
            for u in self.adjacency[t]:
                self.__assert_edge_exists((t, u))
        for t in self.unmarked_adjacency:
            assert (
                len(self.unmarked_adjacency[t]) > 0
            ), "If vertice exists in unmarked adjacency matrix, it must have at least one neighbor"
            for u in self.unmarked_adjacency[t]:
                self.__assert_edge_exists((t, u))
                self.__assert_unmarked_edge_exists((t, u))

    def __assert_edge_exists(self, edge: tuple[int, int]) -> None:
        v, w = edge
        assert (v in self.adjacency) and (
            w in self.adjacency[v]
        ), "Edge must exist in adjacency matrix"
        assert (w in self.adjacency) and (
            v in self.adjacency[w]
        ), "Reciprocal edge must exist in adjacency matrix"

    def __assert_edge_does_not_exist(self, edge: tuple[int, int]) -> None:
        v, w = edge
        assert (v not in self.adjacency) or (
            w not in self.adjacency[v]
        ), "Edge must not exist in adjacency matrix"
        assert (w not in self.adjacency) or (
            v not in self.adjacency[w]
        ), "Reciprocal edge must not exist in adjacency matrix"

    def __assert_unmarked_edge_exists(self, edge: tuple[int, int]) -> None:
        v, w = edge
        assert (v in self.unmarked_adjacency) and (
            w in self.unmarked_adjacency[v]
        ), "Edge must exist in unmarked adjacency matrix"
        assert (w in self.unmarked_adjacency) and (
            v in self.unmarked_adjacency[w]
        ), "Reciprocal edge must exist in unmarked adjacency matrix"

    def __assert_unmarked_edge_does_not_exist(self, edge: tuple[int, int]) -> None:
        v, w = edge
        assert (v not in self.unmarked_adjacency) or (
            w not in self.unmarked_adjacency[v]
        ), "Edge must not exist in unmarked adjacency matrix"
        assert (w not in self.unmarked_adjacency) or (
            v not in self.unmarked_adjacency[w]
        ), "Reciprocal edge must not exist in unmarked adjacency matrix"

    def __assert_vertice_exists(self, vertice: int) -> None:
        assert vertice in self.adjacency, "Vertice must exist in adjacency matrix"

    def __assert_vertice_does_not_exist(self, vertice: int) -> None:
        assert (
            vertice not in self.adjacency
        ), "Vertice must not exist in adjacency matrix"
        assert (
            vertice not in self.unmarked_adjacency
        ), "Vertice must not exist in unmarked adjacency matrix"

    def add_edge(self, edge: tuple[int, int]) -> None:
        self.__assert_edge_does_not_exist(edge)
        self.__assert_unmarked_edge_does_not_exist(edge)
        v, w = edge
        if v not in self.adjacency:
            self.adjacency[v] = set()
        self.adjacency[v].add(w)
        if w not in self.adjacency:
            self.adjacency[w] = set()
        self.adjacency[w].add(v)
        if v not in self.unmarked_adjacency:
            self.unmarked_adjacency[v] = set()
        self.unmarked_adjacency[v].add(w)
        if w not in self.unmarked_adjacency:
            self.unmarked_adjacency[w] = set()
        self.unmarked_adjacency[w].add(v)
        self.__assert_representation()

    def unmark_all_edges(self) -> None:
        self.unmarked_adjacency = copy.deepcopy(self.adjacency)
        self.__assert_representation()

    def mark_edges(self, edges: set[tuple[int, int]]) -> None:
        for edge in edges:
            self.mark_edge(edge)
        self.__assert_representation()

    def mark_edge(self, edge: tuple[int, int]) -> None:
        self.__assert_edge_exists(edge)
        self.__assert_unmarked_edge_exists(edge)
        v, w = edge
        self.unmarked_adjacency[v].remove(w)
        if not self.unmarked_adjacency[v]:
            del self.unmarked_adjacency[v]
        self.unmarked_adjacency[w].remove(v)
        if not self.unmarked_adjacency[w]:
            del self.unmarked_adjacency[w]
        self.__assert_representation()

    def get_unmarked_neighboring_edge(self, vertice: int) -> tuple[int, int] | None:
        self.__assert_representation()
        if vertice in self.unmarked_adjacency:
            return vertice, next(iter(self.unmarked_adjacency[vertice]))
        else:
            return None

    def get_vertices(self) -> list[int]:
        self.__assert_representation()
        return list(self.adjacency.keys())

    def contract(self, blossom: Blossom) -> Graph:
        graph = copy.deepcopy(self)
        blossom_id = id(blossom)
        graph.__assert_vertice_does_not_exist(blossom_id)
        graph.adjacency[blossom_id] = set()
        for t in blossom.get_vertices():
            graph.__assert_vertice_exists(t)
            for u in graph.adjacency[t]:
                graph.__assert_edge_exists((t, u))
                graph.adjacency[u].remove(t)
                if u != blossom_id:
                    graph.adjacency[blossom_id].add(u)
                    graph.adjacency[u].add(blossom_id)
            del graph.adjacency[t]
        if len(graph.adjacency[blossom_id]) == 0:
            # Required to maintain invariant
            del graph.adjacency[blossom_id]
        graph.unmark_all_edges()
        graph.__assert_representation()
        return graph

    def lift_path(self, path: list[int], blossom: Blossom) -> list[int]:
        self.__assert_representation()
        if len(path) == 0:
            return path
        if len(path) == 1:
            assert False, "A path cannot contain exactly one vertice"
        blossom_id = id(blossom)
        if path[0] == blossom_id:

            ############################################################################################################
            # LEFT ENDPOINT
            ############################################################################################################

            #  ,-o                    #    b                    #    o--,
            # |      b  o--o  o--o  o #        o  o--o  o--o  o #        o  o--o  o--o  o
            # o                       # o      |                # b
            #        o                # |      o                #        o
            #    o--'                 #  `-o                    #    o--'

            #  ,-o                    #    o--,
            # |      o  o--o  o--o  o #        o  o--o  o--o  o
            # o      |                # o
            #        o                # |      b
            #    b                    #  `-o

            w = path[1]
            blossom_path: list[int] = []
            for v in blossom.traverse_left():
                blossom_path.append(v)
                if (w in self.adjacency[v]) and (len(blossom_path) % 2 != 0):
                    return blossom_path + path[1:]
            blossom_path = []
            for v in blossom.traverse_right():
                blossom_path.append(v)
                if (w in self.adjacency[v]) and (len(blossom_path) % 2 != 0):
                    return blossom_path + path[1:]
            assert (
                False
            ), "At least one path with even edges must exist through the blossom"
        if path[-1] == blossom_id:

            ############################################################################################################
            # RIGHT ENDPOINT
            ############################################################################################################

            #                    o-.  #                    b    #                 ,--o
            # o  o--o  o--o  b      | # o  o--o  o--o  o        # o  o--o  o--o  o
            #                       o #                |      o #                       b
            #                o        #                o      | #                o
            #                 `--o    #                    o-'  #                 `--o

            #                    o-.  #                 ,--o
            # o  o--o  o--o  o      | # o  o--o  o--o  o
            #                |      o #                       o
            #                o        #                b      |
            #                    b    #                    o-'

            u = path[-2]
            blossom_path = []
            for v in blossom.traverse_left():
                blossom_path.append(v)
                if (u in self.adjacency[v]) and (len(blossom_path) % 2 != 0):
                    return path[:-1] + list(reversed(blossom_path))
            blossom_path = []
            for v in blossom.traverse_right():
                blossom_path.append(v)
                if (u in self.adjacency[v]) and (len(blossom_path) % 2 != 0):
                    return path[:-1] + list(reversed(blossom_path))
            assert (
                False
            ), "At least one path with even edges must exist through the blossom"
        for i, v in enumerate(path):
            if v == blossom_id:
                u, w = path[i - 1], path[i + 1]
                if u in self.adjacency[blossom.get_base()]:

                    ####################################################################################################
                    # INTERIOR LEFT-ORIENTED BLOSSOM
                    ####################################################################################################

                    #            o     #                         #                         #          o--,
                    #                  #                         #                         #              o
                    #            o     #                         #                         # o  o--b
                    #            |     #          o--,           #          o--,           #              o
                    #            o     #              o  o--o  o #              o          #          o--'
                    #                  # o  o--b                 # o  o--b                 #
                    #            o--,  #              o          #              o  o--o  o #          o
                    #                o #          o--'           #          o--'           #          |
                    #   o  o--b        #                         #                         #          o
                    #                o #                         #                         #
                    #            o--'  #                         #                         #          o

                    blossom_path = []
                    for v in blossom.traverse_left():
                        blossom_path.append(v)
                        if (w in self.adjacency[v]) and (len(blossom_path) % 2 != 0):
                            return path[:i] + blossom_path + path[i + 1 :]
                    blossom_path = []
                    for v in blossom.traverse_right():
                        blossom_path.append(v)
                        if (w in self.adjacency[v]) and (len(blossom_path) % 2 != 0):
                            return path[:i] + blossom_path + path[i + 1 :]
                    assert (
                        False
                    ), "At least one path with even edges must exist through the blossom"
                elif w in self.adjacency[blossom.get_base()]:

                    ####################################################################################################
                    # INTERIOR RIGHT-ORIENTED BLOSSOM
                    ####################################################################################################

                    #       o          #                         #                         #  ,--o
                    #                  #                         #                         # o
                    #       o          #                         #                         #        b--o  o
                    #       |          #           ,--o          #           ,--o          # o
                    #       o          # o  o--o  o              #          o              #  `--o
                    #                  #                 b--o  o #                 b--o  o #
                    #    ,--o          #          o              # o  o--o  o              #     o
                    #   o              #           `--o          #           `--o          #     |
                    #          b--o  o #                         #                         #     o
                    #   o              #                         #                         #
                    #    `--o          #                         #                         #     o

                    blossom_path = []
                    for v in blossom.traverse_left():
                        blossom_path.append(v)
                        if (u in self.adjacency[v]) and (len(blossom_path) % 2 != 0):
                            return (
                                path[:i] + list(reversed(blossom_path)) + path[i + 1 :]
                            )
                    blossom_path = []
                    for v in blossom.traverse_right():
                        blossom_path.append(v)
                        if (u in self.adjacency[v]) and (len(blossom_path) % 2 != 0):
                            return (
                                path[:i] + list(reversed(blossom_path)) + path[i + 1 :]
                            )
                    assert (
                        False
                    ), "At least one path with even edges must exist through the blossom"
                else:
                    assert (
                        False
                    ), "Exactly one side of the path must be incident to the base of the blossom"
        return path


class Matching:
    def __init__(self, vertices: list[int]) -> None:
        self.adjacency = dict[int, set[int]]()
        self.edges = set[tuple[int, int]]()
        self.exposed_vertices = set[int]()
        self.add_vertices(vertices)
        self.__assert_representation()

    def __assert_representation(self) -> None:
        for t in self.adjacency:
            self.__assert_vertice_exists(t)
            if len(self.adjacency[t]) == 0:
                self.__assert_vertice_is_exposed(t)
            else:
                self.__assert_vertice_is_not_exposed(t)
                u = next(iter(self.adjacency[t]))
                edge = (t, u) if t < u else (u, t)
                self.__assert_edge_exists(edge)
                self.__assert_vertice_is_not_exposed(u)

    def __assert_edge_exists(self, edge: tuple[int, int]) -> None:
        v, w = edge
        assert (v in self.adjacency) and (
            w in self.adjacency[v]
        ), "Edge must exist in adjacency matrix"
        assert (w in self.adjacency) and (
            v in self.adjacency[w]
        ), "Reciprocal edge must exist in adjacency matrix"
        assert edge in self.edges, "Edge must exist in edges set"

    def __assert_edge_does_not_exist(self, edge: tuple[int, int]) -> None:
        v, w = edge
        assert (v not in self.adjacency) or (
            w not in self.adjacency[v]
        ), "Edge must not exist in adjacency matrix"
        assert (w not in self.adjacency) or (
            v not in self.adjacency[w]
        ), "Reciprocal edge must not exist in adjacency matrix"
        assert edge not in self.edges, "Edge must not exist in edges set"

    def __assert_vertice_is_exposed(self, vertice: int) -> None:
        assert vertice in self.adjacency, "Vertice must exist in adjacency matrix"
        assert (
            vertice in self.exposed_vertices
        ), "Vertice must exist in exposed vertices set"
        assert len(self.adjacency[vertice]) == 0, "Vertice must have no neighbors"

    def __assert_vertice_is_not_exposed(self, vertice: int) -> None:
        assert vertice in self.adjacency, "Vertice must exist in adjacency matrix"
        assert (
            vertice not in self.exposed_vertices
        ), "Vertice must not exist in exposed vertices set"
        assert (
            len(self.adjacency[vertice]) == 1
        ), "Vertice must have exactly one neighbor"

    def __assert_vertice_exists(self, vertice: int) -> None:
        assert vertice in self.adjacency, "Vertice must exist in adjacency matrix"
        if vertice in self.exposed_vertices:
            assert (
                len(self.adjacency[vertice]) == 0
            ), "If vertice is exposed, it must have no neighbors"
        else:
            assert (
                len(self.adjacency[vertice]) == 1
            ), "If vertice is not exposed, it must have exactly one neighbor"

    def __assert_vertice_does_not_exist(self, vertice: int) -> None:
        assert (
            vertice not in self.adjacency
        ), "Vertice must not exist in adjacency matrix"
        assert vertice not in self.exposed_vertices, "Vertice must not be exposed"

    def augment(self, path: list[int]) -> Matching:
        self.__assert_vertice_is_exposed(path[0])
        self.__assert_vertice_is_exposed(path[-1])
        self.exposed_vertices.remove(path[0])
        self.exposed_vertices.remove(path[-1])
        for i in range(len(path) - 1):
            v, w = path[i], path[i + 1]
            edge = (v, w) if v < w else (w, v)
            if edge in self.edges:
                self.__assert_edge_exists(edge)
                self.edges.remove(edge)
                self.adjacency[v].remove(w)
                self.adjacency[w].remove(v)
            else:
                self.__assert_edge_does_not_exist(edge)
                self.edges.add(edge)
                self.adjacency[v].add(w)
                self.adjacency[w].add(v)
        self.__assert_representation()
        return self

    def get_edges(self) -> set[tuple[int, int]]:
        self.__assert_representation()
        return self.edges

    def get_exposed_vertices(self) -> set[int]:
        self.__assert_representation()
        return self.exposed_vertices

    def get_matched_vertice(self, vertice: int) -> int:
        self.__assert_representation()
        self.__assert_vertice_is_not_exposed(vertice)
        return next(iter(self.adjacency[vertice]))

    def add_vertices(self, vertices: list[int]) -> None:
        for vertice in vertices:
            self.add_vertice(vertice)
        self.__assert_representation()

    def add_vertice(self, vertice: int) -> None:
        self.__assert_vertice_does_not_exist(vertice)
        self.adjacency[vertice] = set()
        self.exposed_vertices.add(vertice)
        self.__assert_representation()

    def contract(self, blossom: Blossom) -> Matching:
        matching = copy.deepcopy(self)
        blossom_id = id(blossom)
        matching.__assert_vertice_does_not_exist(blossom_id)
        matching.adjacency[blossom_id] = set()
        if blossom.get_base() in matching.exposed_vertices:
            matching.exposed_vertices.add(blossom_id)
        for t in blossom.get_vertices():
            matching.__assert_vertice_exists(t)
            for u in matching.adjacency[t]:
                e = (t, u) if t < u else (u, t)
                matching.__assert_edge_exists(e)
                matching.edges.remove(e)
                matching.adjacency[u].remove(t)
                if u != blossom_id:
                    new_edge = (blossom_id, u) if blossom_id < u else (u, blossom_id)
                    matching.edges.add(new_edge)
                    matching.adjacency[blossom_id].add(u)
                    matching.adjacency[u].add(blossom_id)
            del matching.adjacency[t]
            matching.exposed_vertices.discard(t)
        matching.__assert_representation()
        return matching


class Forest:
    def __init__(self, roots: set[int]) -> None:
        self.distances_to_root = dict[int, int]()
        self.unmarked_even_vertices = set[int]()
        self.parents = dict[int, int]()
        self.roots = dict[int, int]()
        for root in roots:
            self.add_singleton_tree(root)
        self.__assert_representation()

    def __assert_representation(self) -> None:
        for vertice in self.roots:
            self.__assert_vertice_exists(vertice)
        assert (
            self.roots.keys() == self.distances_to_root.keys()
        ), "Roots and distances to root must have same keys"
        assert (
            self.roots.keys() == self.parents.keys()
        ), "Roots and parents mut have same keys"
        for vertice in self.unmarked_even_vertices:
            self.__assert_vertice_exists(vertice)
            assert (
                self.distances_to_root[vertice] % 2 == 0
            ), "Unmarked even vertice must have even distance to root"

    def __assert_vertice_exists(self, vertice: int) -> None:
        assert vertice in self.roots, "Vertice must have a root"
        assert vertice in self.distances_to_root, "Vertice must have a distance to root"
        assert vertice in self.parents, "Vertice must have a parent"

    def __assert_vertice_does_not_exist(self, vertice: int) -> None:
        assert vertice not in self.roots, "Vertice must not have a root"
        assert (
            vertice not in self.distances_to_root
        ), "Vertice must not have a distance to root"
        assert (
            vertice not in self.unmarked_even_vertices
        ), "Vertice must not exist in unmarked even vertices set"
        assert vertice not in self.parents, "Vertice must not have a parent"

    def add_singleton_tree(self, vertice: int) -> None:
        self.__assert_vertice_does_not_exist(vertice)
        self.roots[vertice] = vertice
        self.distances_to_root[vertice] = 0
        self.unmarked_even_vertices.add(vertice)
        self.parents[vertice] = vertice
        self.__assert_representation()

    def get_unmarked_even_vertice(self) -> int | None:
        self.__assert_representation()
        if len(self.unmarked_even_vertices) > 0:
            return next(iter(self.unmarked_even_vertices))
        else:
            return None

    def mark_vertice(self, vertice: int) -> None:
        self.__assert_vertice_exists(vertice)
        if self.distances_to_root[vertice] % 2 == 0:
            assert (
                vertice in self.unmarked_even_vertices
            ), "If vertice has an even distance to root, it must exist in unmarked even vertices set"
            self.unmarked_even_vertices.remove(vertice)
        self.__assert_representation()

    def does_contain_vertice(self, vertice: int) -> bool:
        self.__assert_representation()
        return vertice in self.roots

    def add_edge(self, edge: tuple[int, int]) -> None:
        v, w = edge
        self.__assert_vertice_does_not_exist(w)
        self.__assert_vertice_exists(v)
        self.roots[w] = self.roots[v]
        self.distances_to_root[w] = 1 + self.distances_to_root[v]
        if self.distances_to_root[w] % 2 == 0:
            self.unmarked_even_vertices.add(w)
        self.parents[w] = v
        self.__assert_representation()

    def get_distance_to_root(self, vertice: int) -> int:
        self.__assert_representation()
        self.__assert_vertice_exists(vertice)
        return self.distances_to_root[vertice]

    def get_root(self, vertice: int) -> int:
        self.__assert_representation()
        self.__assert_vertice_exists(vertice)
        return self.roots[vertice]

    def get_path_from_root_to(self, vertice: int) -> list[int]:
        self.__assert_representation()
        return list(reversed(self.get_path_to_root_from(vertice)))

    def get_path_to_root_from(self, vertice: int) -> list[int]:
        self.__assert_representation()
        self.__assert_vertice_exists(vertice)
        path = list[int]()
        while self.parents[vertice] != vertice:
            path.append(vertice)
            vertice = self.parents[vertice]
        path.append(vertice)
        assert len(set(path)) == len(
            path
        ), "Path to root must not contain any duplicate vertices"
        return path

    def get_blossom(self, v: int, w: int) -> Blossom:
        self.__assert_representation()
        v_path = self.get_path_to_root_from(v)
        w_path = self.get_path_to_root_from(w)
        w_ancestors = set(w_path)
        v_blossom_vertices = list[int]()
        common_ancestor = None
        for u in v_path:
            if u in w_ancestors:
                common_ancestor = u
                break
            else:
                v_blossom_vertices.append(u)
        assert common_ancestor is not None, "Common ancestor must exist"
        w_blossom_vertices = list[int]()
        for u in w_path:
            if u == common_ancestor:
                break
            else:
                w_blossom_vertices.append(u)
        blossom_vertices = (
            [common_ancestor] + list(reversed(v_blossom_vertices)) + w_blossom_vertices
        )
        assert len(set(blossom_vertices)) == len(
            blossom_vertices
        ), "Blossom must not contain any duplicate vertices"
        assert (
            len(blossom_vertices) % 2 != 0
        ), "Blossom must contain an odd number of vertices"
        blossom = Blossom(blossom_vertices, common_ancestor)
        return blossom


class Blossom:
    def __init__(self, vertices: list[int], base: int) -> None:
        self.vertices = vertices
        self.base = base
        self.__assert_representation()

    def __assert_representation(self) -> None:
        assert self.vertices[0] == self.base, "Blossom must begin with base vertice"
        assert (
            len(self.vertices) % 2 != 0
        ), "Blossom must have an odd number of vertices"
        assert len(self.vertices) >= 3, "Blossom must have at least three vertices"

    def get_vertices(self) -> list[int]:
        self.__assert_representation()
        return self.vertices

    def get_base(self) -> int:
        self.__assert_representation()
        return self.base

    def traverse_right(self) -> Generator[int, None, None]:
        self.__assert_representation()
        yield from self.vertices

    def traverse_left(self) -> Generator[int, None, None]:
        self.__assert_representation()
        yield from reversed(self.vertices[1:] + self.vertices[:1])
