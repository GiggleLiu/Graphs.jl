struct GraphMatcher
end

# VF2 Algorithm
function GraphMatcher(G1, G2)
    self.G1 = G1
    self.G2 = G2
    self.G1_nodes = set(G1.nodes())
    self.G2_nodes = set(G2.nodes())
    self.G2_node_order = {n: i for i, n in enumerate(G2)}

    # Set recursion limit.
    self.old_recursion_limit = sys.getrecursionlimit()
    expected_max_recursion_level = len(self.G2)
    if self.old_recursion_limit < 1.5 * expected_max_recursion_level
        # Give some breathing room.
        sys.setrecursionlimit(int(1.5 * expected_max_recursion_level))
    end

    # Declare that we will be searching for a graph-graph isomorphism.
    self.test = "graph"

    ############## Initialize state ################
    # core_1[n] contains the index of the node paired with n, which is m,
    #           provided n is in the mapping.
    # core_2[m] contains the index of the node paired with m, which is n,
    #           provided m is in the mapping.
    self.core_1 = {}
    self.core_2 = {}

    # See the paper for definitions of M_x and T_x^{y}

    # inout_1[n]  is non-zero if n is in M_1 or in T_1^{inout}
    # inout_2[m]  is non-zero if m is in M_2 or in T_2^{inout}
    #
    # The value stored is the depth of the SSR tree when the node became
    # part of the corresponding set.
    self.inout_1 = {}
    self.inout_2 = {}
    # Practically, these sets simply store the nodes in the subgraph.

    self.state = GMState(self)

    # Provide a convenient way to access the isomorphism mapping.
    self.mapping = self.core_1.copy()
end

# Restores the recursion limit.
function reset_recursion_limit(self)
    sys.setrecursionlimit(self.old_recursion_limit)
end

function candidate_pairs_iter(self)
    G1_nodes = self.G1_nodes
    G2_nodes = self.G2_nodes
    min_key = self.G2_node_order.__getitem__

    # First we compute the inout-terminal sets.
    T1_inout = [node for node in self.inout_1 if node not in self.core_1]
    T2_inout = [node for node in self.inout_2 if node not in self.core_2]

    # If T1_inout and T2_inout are both nonempty.
    # P(s) = T1_inout x {min T2_inout}
    if T1_inout && T2_inout
        node_2 = min(T2_inout, key=min_key)
        for node_1 in T1_inout
            yield node_1, node_2
        end

    else
        # If T1_inout and T2_inout were both empty....
        # P(s) = (N_1 - M_1) x {min (N_2 - M_2)}
        # if not (T1_inout or T2_inout):  # as suggested by  [2], incorrect
        if true  # as inferred from [1], correct
            # First we determine the candidate node for G2
            other_node = min(G2_nodes - set(self.core_2), key=min_key)
            for node in self.G1
                if node not in self.core_1
                    yield node, other_node
                end
            end
        end
    end
end

# For all other cases, we don't have any candidate pairs.


function is_isomorphic(gm::GraphMatcher)
    """Returns true if G1 and G2 are isomorphic graphs."""

    # Let's do two very quick checks!
    # QUESTION: Should we call faster_graph_could_be_isomorphic(G1,G2)?
    # For now, I just copy the code.

    # Check global properties
    if gm.G1.order() != gm.G2.order():
        return false

    # Check local properties
    d1 = sorted(d for n, d in gm.G1.degree())
    d2 = sorted(d for n, d in gm.G2.degree())
    if d1 != d2
        return false
    end

    try
        x = next(gm.isomorphisms_iter())
        return true
    catch StopIteration
        return false
    end
end


function isomorphisms_iter(gm)
    """Generator over isomorphisms between G1 and G2."""
    # Declare that we are looking for a graph-graph isomorphism.
    self.test = "graph"
    self.initialize()
    yield from self.match()
end


function match(self)
    """Extends the isomorphism mapping.

    This function is called recursively to determine if a complete
    isomorphism can be found between G1 and G2.  It cleans up the class
    variables after each recursive call. If an isomorphism is found,
    we yield the mapping.

    """
    if len(self.core_1) == len(self.G2):
        # Save the final mapping, otherwise garbage collection deletes it.
        self.mapping = self.core_1.copy()
        # The mapping is complete.
        yield self.mapping
    else:
        for G1_node, G2_node in self.candidate_pairs_iter():
            if self.syntactic_feasibility(G1_node, G2_node):
                if self.semantic_feasibility(G1_node, G2_node):
                    # Recursive call, adding the feasible state.
                    newstate = self.state.__class__(self, G1_node, G2_node)
                    yield from self.match()

                    # restore data structures
                    newstate.restore()


def semantic_feasibility(self, G1_node, G2_node):
    """Returns true if adding (G1_node, G2_node) is symantically feasible.

    The semantic feasibility function should return true if it is
    acceptable to add the candidate pair (G1_node, G2_node) to the current
    partial isomorphism mapping.   The logic should focus on semantic
    information contained in the edge data or a formalized node class.

    By acceptable, we mean that the subsequent mapping can still become a
    complete isomorphism mapping.  Thus, if adding the candidate pair
    definitely makes it so that the subsequent mapping cannot become a
    complete isomorphism mapping, then this function must return false.

    The default semantic feasibility function always returns true. The
    effect is that semantics are not considered in the matching of G1
    and G2.

    The semantic checks might differ based on the what type of test is
    being performed.  A keyword description of the test is stored in
    self.test.  Here is a quick description of the currently implemented
    tests::

        test='graph'
        Indicates that the graph matcher is looking for a graph-graph
        isomorphism.

        test='subgraph'
        Indicates that the graph matcher is looking for a subgraph-graph
        isomorphism such that a subgraph of G1 is isomorphic to G2.

        test='mono'
        Indicates that the graph matcher is looking for a subgraph-graph
        monomorphism such that a subgraph of G1 is monomorphic to G2.

    Any subclass which redefines semantic_feasibility() must maintain
    the above form to keep the match() method functional. Implementations
    should consider multigraphs.
    """
    return true

[docs]    def subgraph_is_isomorphic(self):
    """Returns true if a subgraph of G1 is isomorphic to G2."""
    try:
        x = next(self.subgraph_isomorphisms_iter())
        return true
    except StopIteration:
        return false


def subgraph_is_monomorphic(self):
    """Returns true if a subgraph of G1 is monomorphic to G2."""
    try:
        x = next(self.subgraph_monomorphisms_iter())
        return true
    except StopIteration:
        return false

#    subgraph_is_isomorphic.__doc__ += "\n" + subgraph.replace('\n','\n'+indent)

[docs]    def subgraph_isomorphisms_iter(self):
    """Generator over isomorphisms between a subgraph of G1 and G2."""
    # Declare that we are looking for graph-subgraph isomorphism.
    self.test = "subgraph"
    self.initialize()
    yield from self.match()


def subgraph_monomorphisms_iter(self):
    """Generator over monomorphisms between a subgraph of G1 and G2."""
    # Declare that we are looking for graph-subgraph monomorphism.
    self.test = "mono"
    self.initialize()
    yield from self.match()

#    subgraph_isomorphisms_iter.__doc__ += "\n" + subgraph.replace('\n','\n'+indent)

[docs]    def syntactic_feasibility(self, G1_node, G2_node):
    """Returns true if adding (G1_node, G2_node) is syntactically feasible.

    This function returns true if it is adding the candidate pair
    to the current partial isomorphism/monomorphism mapping is allowable.
    The addition is allowable if the inclusion of the candidate pair does
    not make it impossible for an isomorphism/monomorphism to be found.
    """

    # The VF2 algorithm was designed to work with graphs having, at most,
    # one edge connecting any two nodes.  This is not the case when
    # dealing with an MultiGraphs.
    #
    # Basically, when we test the look-ahead rules R_neighbor, we will
    # make sure that the number of edges are checked. We also add
    # a R_self check to verify that the number of selfloops is acceptable.
    #
    # Users might be comparing Graph instances with MultiGraph instances.
    # So the generic GraphMatcher class must work with MultiGraphs.
    # Care must be taken since the value in the innermost dictionary is a
    # singlet for Graph instances.  For MultiGraphs, the value in the
    # innermost dictionary is a list.

    ###
    # Test at each step to get a return value as soon as possible.
    ###

    # Look ahead 0

    # R_self

    # The number of selfloops for G1_node must equal the number of
    # self-loops for G2_node. Without this check, we would fail on
    # R_neighbor at the next recursion level. But it is good to prune the
    # search tree now.

    if self.test == "mono":
        if self.G1.number_of_edges(G1_node, G1_node) < self.G2.number_of_edges(
            G2_node, G2_node
        ):
            return false
    else:
        if self.G1.number_of_edges(G1_node, G1_node) != self.G2.number_of_edges(
            G2_node, G2_node
        ):
            return false

    # R_neighbor

    # For each neighbor n' of n in the partial mapping, the corresponding
    # node m' is a neighbor of m, and vice versa. Also, the number of
    # edges must be equal.
    if self.test != "mono":
        for neighbor in self.G1[G1_node]:
            if neighbor in self.core_1:
                if not (self.core_1[neighbor] in self.G2[G2_node]):
                    return false
                elif self.G1.number_of_edges(
                    neighbor, G1_node
                ) != self.G2.number_of_edges(self.core_1[neighbor], G2_node):
                    return false

    for neighbor in self.G2[G2_node]:
        if neighbor in self.core_2:
            if not (self.core_2[neighbor] in self.G1[G1_node]):
                return false
            elif self.test == "mono":
                if self.G1.number_of_edges(
                    self.core_2[neighbor], G1_node
                ) < self.G2.number_of_edges(neighbor, G2_node):
                    return false
            else:
                if self.G1.number_of_edges(
                    self.core_2[neighbor], G1_node
                ) != self.G2.number_of_edges(neighbor, G2_node):
                    return false

    if self.test != "mono":
        # Look ahead 1

        # R_terminout
        # The number of neighbors of n in T_1^{inout} is equal to the
        # number of neighbors of m that are in T_2^{inout}, and vice versa.
        num1 = 0
        for neighbor in self.G1[G1_node]:
            if (neighbor in self.inout_1) and (neighbor not in self.core_1):
                num1 += 1
        num2 = 0
        for neighbor in self.G2[G2_node]:
            if (neighbor in self.inout_2) and (neighbor not in self.core_2):
                num2 += 1
        if self.test == "graph":
            if not (num1 == num2):
                return false
        else:  # self.test == 'subgraph'
            if not (num1 >= num2):
                return false

        # Look ahead 2

        # R_new

        # The number of neighbors of n that are neither in the core_1 nor
        # T_1^{inout} is equal to the number of neighbors of m
        # that are neither in core_2 nor T_2^{inout}.
        num1 = 0
        for neighbor in self.G1[G1_node]:
            if neighbor not in self.inout_1:
                num1 += 1
        num2 = 0
        for neighbor in self.G2[G2_node]:
            if neighbor not in self.inout_2:
                num2 += 1
        if self.test == "graph":
            if not (num1 == num2):
                return false
        else:  # self.test == 'subgraph'
            if not (num1 >= num2):
                return false

    # Otherwise, this node pair is syntactically feasible!
    return true
