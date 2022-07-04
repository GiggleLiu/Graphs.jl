using Graphs, StatsBase

function line_graph(G::SimpleGraph)
    vs =  collect(edges(G))
    n = length(vs)
    L = SimpleGraph(n)
    for i=1:n
        v = vs[i]
        for j=i+1:n
            u = vs[j]
            if v.src == u.src || v.dst == u.src || v.src == u.dst || v.dst == u.dst
                add_edge!(L, i, j)
            end
        end
    end
    return L
end

# NOTE: copied from networkx.
function inverse_line_graph(G)
    if nv(G) == 0
        return SimpleGraph(1)
    elseif nv(G) == 1
        v = arbitrary_element(G)
        a = (v, 0)
        b = (v, 1)
        H = SimpleGraph([Edge(a, b)])
        return H
    elseif nv(G) > 1 && ne(G) == 0
        error(
            "inverse_line_graph() doesn't work on an edgeless graph. Please use this function on each component seperately."
        )
    end

    starting_cell = _select_starting_cell(G)
    P = _find_partition(G, starting_cell)
    # count how many times each vertex appears in the partition set
    P_count = zeros(Int, nv(G))
    for p in P, u in p
        P_count[u] += 1
    end

    if maximum(P_count) > 2
        error("G is not a line graph (vertex found in more than two partition cells)")
    end
    W = [(u,) for u in P_count if P_count[u] == 1]
    nodes = [P..., W...]
    n = length(nodes)
    H = SimpleGraph(n)
    for i=1:n
        for j=i+1:n
            if any(a_bit->a_bit ∈ nodes[j], nodes[i])
                add_edge!(H, i, j)
            end
        end
    end
    return H
end

# Find a partition of the vertices of G into cells of complete graphs
function _find_partition(G, starting_cell)
    G_partition = copy(G)
    P = [starting_cell]  # partition set
    rem_cell!(G_partition, starting_cell)
    # keep list of partitioned nodes which might have an edge in G_partition
    partitioned_vertices = collect(starting_cell)
    while ne(G_partition) > 0 
        # there are still edges left and so more cells to be made
        u = partitioned_vertices[end]
        deg_u = degree(G_partition, u)
        if deg_u == 0
            # if u has no edges left in G_partition then we have found
            # all of its cells so we do not need to keep looking
            pop!(partitioned_vertices)
        else
            # if u still has edges then we need to find its other cell
            # this other cell must be a complete subgraph or else G is
            # not a line graph
            new_cell = [u, neighbors(G_partition, u)...]
            for u in new_cell
                for v in new_cell
                    if (u != v) && !has_edge(G_partition, u, v)
                        error("G is not a line graph (partition cell not a complete subgraph)")
                    end
                end
            end
            push!(P, (new_cell...,))
            rem_cell!(G_partition, new_cell)
            append!(partitioned_vertices, new_cell)
        end
    end
    return P
end

function rem_cell!(g, cell)
    for i=1:length(cell), j=i+1:length(cell)
        rem_edge!(g, cell[i], cell[j])
    end
end


# Select a cell to initiate _find_partition
# If starting edge not specified then pick an arbitrary edge - doesn't
# matter which. However, this function may call itself requiring a
# specific starting edge. Note that the r, s notation for counting
# triangles is the same as in the Roussopoulos paper cited above.
function _select_starting_cell(G, starting_edge=nothing)
    if starting_edge === nothing
        e = rand(collect(edges(G)))
    else
        e = starting_edge
        if !has_edge(G, e)
            error("starting_edge $e is not in the Graph")
        end
    end
    e_triangles = _triangles(G, e.src, e.dst)
    r = length(e_triangles)
    if r == 0
        # there are no triangles containing e, so the starting cell is just e
        starting_cell = e
    elseif r == 1
        # there is exactly one triangle, T, containing e. If other 2 edges
        # of T belong only to this triangle then T is starting cell
        T = e_triangles[1]
        a, b, c = T
        # ab was original edge so check the other 2 edges
        ac_edges = _triangles(G, a, c)
        bc_edges = _triangles(G, b, c)
        if length(ac_edges) == 1
            if length(bc_edges) == 1
                starting_cell = T
            else
                return _select_starting_cell(G, starting_edge=Edge(b, c))
            end
        else
            return _select_starting_cell(G, starting_edge=Edge(a, c))
        end
    else
        # r >= 2 so we need to count the number of odd triangles, s
        s = 0
        odd_triangles = Tuple{Int,Int,Int}[]
        for T in e_triangles
            if _odd_triangle(G, T)
                s += 1
                push!(odd_triangles, T)
            end
        end
        if r == 2 && s == 0
            # in this case either triangle works, so just use T
            starting_cell = T
        elseif r - 1 <= s <= r
            # check if odd triangles containing e form complete subgraph
            # there must be exactly s+2 of them
            # and they must all be connected
            triangle_nodes = unique!(vcat(collect.(odd_triangles)...))
            if length(triangle_nodes) == s + 2
                for u in triangle_nodes, v in triangle_nodes
                    if u != v && !has_edge(G, u, v)
                        error("G is not a line graph (odd triangles do not form complete subgraph)")
                    end
                end
                # otherwise then we can use this as the starting cell
                starting_cell = (triangle_nodes...,)
            else
                error("G is not a line graph (odd triangles do not form complete subgraph)")
            end
        else
            error("G is not a line graph (incorrect number of odd triangles around starting edge)")
        end
    end
    return starting_cell
end

# Return list of all triangles containing edge e
function _triangles(G, u, v)
    !has_edge(G, u, v) && error("Edge ($u, $v) not in graph")
    triangle_list = Tuple{Int,Int,Int}[]
    for x in neighbors(G, u)
        if has_edge(G, v, x)
            push!(triangle_list, (u, v, x))
        end
    end
    return triangle_list
end

# Test whether T is an odd triangle in G
# An odd triangle is one in which there exists another vertex in G which is
# adjacent to either exactly one or exactly all three of the vertices in the
# triangle.
function _odd_triangle(G, T)
    if !has_edge(G, T[1], T[2]) || !has_edge(G, T[3], T[2]) || !has_edge(G, T[3], T[1])
        error("Edge $e not in graph")
    end

    T_neighbors = zeros(Int, nv(G))
    for t in T
        for v in neighbors(G, t)
            if v ∉ T
                T_neighbors[v] += 1
            end
        end
    end
    return any(c -> c==1 || c==3, T_neighbors)
end

using Test
@testset "triangles" begin
    g = complete_graph(5)
    @test _triangles(g, 2, 4) |> length == 3
    @test _odd_triangle(g, (1,2,4))
    @test _select_starting_cell(g, Edge(1,2))  == (1,2,3,4,5)
    starting_cell = (1,2,3,4,5)
    @show _find_partition(g, starting_cell)
end

@testset "line graph" begin
    g = smallgraph(:petersen)
    ig = line_graph(g)
    @test nv(ig) == 15
    @test ne(ig) == 30
    gg = inverse_line_graph(ig)
    @test nv(gg) == 10
    @test ne(gg) == 15
end