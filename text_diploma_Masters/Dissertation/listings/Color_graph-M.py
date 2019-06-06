from copy import deepcopy
from datetime import datetime


# Read graph
max_vertice = 1345

def read(path = 'graphs_txt/M_edges.txt'):    
    vertex_neigh = [[] for _ in range(max_vertice+1)]
    edges = []
    vertices = set()

    f = open(path, 'r')
    lines = f.readlines()
    for line in lines:
        fst = int(line.split(',')[0][1:])
        snd = int(line.split(',')[1][:-2])
        edges.append((fst, snd))
        vertices.add(fst)
        vertices.add(snd)

        vertex_neigh[fst].append(snd)
        vertex_neigh[snd].append(fst)
    return sorted(list(vertices)), vertex_neigh, edges, 

vertices, vertex_neigh, edges = read()
print('vertices:', vertices[:5])
print('vertex_neigh:', vertex_neigh[:5])
print('edges: ', edges[:5])

print('len(vertices):', len(vertices))
print('len(vertex_neigh):', len(vertex_neigh))
print('len(edges): ', len(edges))


#Count triangles

# every triangle occures in triangles 3 times: one for every sorted edge coming first
def count_triangles(vertex_neigh, edges):
    number_of_triangles_vertex_is_in = [0 for _ in range(max_vertice+1)]
    triangles = []
    edge_to_third = {}
    
    for edge in edges:
        fst, snd = edge[0], edge[1]
        trds = set(vertex_neigh[fst]).intersection(set(vertex_neigh[snd] ))
        edge_to_third[(fst, snd)] = trds
        number_of_triangles_vertex_is_in[fst] += len(trds)
        number_of_triangles_vertex_is_in[snd] += len(trds)
        for trd in trds:
            triangles.append((fst, snd, trd))
    number_of_triangles_vertex_is_in = [item / 2 for item in number_of_triangles_vertex_is_in]
    return triangles, edge_to_third, number_of_triangles_vertex_is_in

triangles, edge_to_third, number_of_triangles_vertex_is_in = count_triangles(vertex_neigh, edges)
print('triangles:', triangles[:5])
print('edge_to_third:', ['{' + str(key) + ': '+ str(edge_to_third[key]) + '}' for key in edge_to_third.keys()][:5])
print('number_of_triangles_vertex_is_in:', number_of_triangles_vertex_is_in[:5])
assert(sum(number_of_triangles_vertex_is_in) == len(triangles))
assert(sum([len(edge_to_third[key]) for key in edge_to_third.keys()]) == len(triangles))


# Count spindles

def count_spindles(vertex_neigh, edges, edge_to_third):
    number_of_spindles_vertex_is_in = [0 for _ in range(max_vertice+1)]
    count = 0
    for edge_first in edges:
        for edge_second in edges:
            uppers = edge_to_third[edge_first].intersection(edge_to_third[edge_second])
            for upper in uppers:
                for lower_left in edge_to_third[edge_first]:
                    if lower_left != upper:
                        lower_rights = set(vertex_neigh[lower_left]).intersection(edge_to_third[edge_second] - {upper})
                        
                        number_of_spindles_vertex_is_in[edge_first[0]] += len(lower_rights)
                        number_of_spindles_vertex_is_in[edge_first[1]] += len(lower_rights)
                        number_of_spindles_vertex_is_in[edge_second[0]] += len(lower_rights)
                        number_of_spindles_vertex_is_in[edge_second[1]] += len(lower_rights)
                        number_of_spindles_vertex_is_in[upper] += len(lower_rights)
                        number_of_spindles_vertex_is_in[lower_left] += len(lower_rights)
                        for item in list(lower_rights):
                            number_of_spindles_vertex_is_in[lower_left] += 1
                        
                        count += len(lower_rights)
    return count, number_of_spindles_vertex_is_in

print('Started:', datetime.now())
spindles_count, number_of_spindles_vertex_is_in = count_spindles(vertex_neigh, edges, edge_to_third)
print('Finished:', datetime.now())

print('spindles_count:', spindles_count)
print('number_of_spindles_vertex_is_in:', number_of_spindles_vertex_is_in[:5])
assert(spindles_count == sum(number_of_spindles_vertex_is_in)/7)


# Sort vertices

def sort(vertices, vertex_neigh, number_of_triangles_vertex_is_in, number_of_spindles_vertex_is_in):
    return sorted(vertices, key=lambda x: 
                  (number_of_spindles_vertex_is_in[x], len(vertex_neigh[x]), number_of_triangles_vertex_is_in[x]), 
                  reverse=True)

sorted_vertices = sort(list(range(1, max_vertice+1)), vertex_neigh, number_of_triangles_vertex_is_in, number_of_spindles_vertex_is_in)
print('sorted_vertices:', sorted_vertices[:10])
print('number_of_spindles_vertex_is_in in sorted order:', 
      [(number_of_spindles_vertex_is_in[item], len(vertex_neigh[item]), number_of_triangles_vertex_is_in[item]) 
           for item in sorted_vertices[:5]])
for i in range(1, len(sorted_vertices)):
    assert(number_of_spindles_vertex_is_in[sorted_vertices[i-1]] >= number_of_spindles_vertex_is_in[sorted_vertices[i]])


# Coloring algorithm
def get_next(sorted_vertices, colors_already, verbose=False):
    for item in sorted_vertices:
        if colors_already[item] == -1:
            if verbose:
                print('Free coloring', item)
            return item
    return None

# all forced, no choice here
# return None -> no coloring with given colors_already, colors_available
# return colors_already, colors_available -> ok, choose next vertex
def process_just_colored_bfs(vertex, vertex_neigh, colors_already, colors_available, verbose=False):
    queue_to_process = [vertex]

    while len(queue_to_process) > 0:
        vertex = queue_to_process[0]
        queue_to_process = queue_to_process[1:]
        color = colors_already[vertex]
        if verbose:
            print('process_just_colored', vertex)
        for v in vertex_neigh[vertex]:
            if color in colors_available[v]:
                colors_available[v].remove(color)
            if len(colors_available[v]) == 0:
                if verbose:
                    print('backtrack', v)
                return None
            elif len(colors_available[v]) == 1 and colors_already[v] == -1:
                colors_already[v] = list(colors_available[v])[0]
                queue_to_process.append(v)
    return colors_already, colors_available



def do_color(sorted_vertices, vertex_neigh, colors_already, colors_available, verbose=False):
    next_vert = get_next(sorted_vertices, colors_already, verbose)
    if next_vert == None:
        return colors_already, colors_available
    else:
        for color in colors_available[next_vert]:
            if verbose:
                print('Try', color, 'for', next_vert)
            new_colors_already = deepcopy(colors_already)
            new_colors_available = deepcopy(colors_available)

            new_colors_already[next_vert] = color
            new_colors_available[next_vert] = {color}
            processed = process_just_colored_bfs(next_vert, vertex_neigh, new_colors_already, new_colors_available, verbose)
            if processed == None:
                pass
            else:
                new_colors_already, new_colors_available = processed[0], processed[1]
                res = do_color(sorted_vertices, vertex_neigh, new_colors_already, new_colors_available, verbose)
                if res != None:
                    return res
        return None


# Essentially distinct ways to color H with at most  4 colors
ways_to_color_H = [
#     Monochromatic
    [1, 2, 3, 2, 3, 2, 3],
    [1, 2, 4, 2, 3, 2, 3],
    
#     Non-monochromatic
    [1, 2, 3, 2, 4, 3, 4],
    [1, 2, 3, 4, 2, 3, 4],
]
Hs_start = [1, 2, 3, 4, 5, 6, 7]


# Color the graph
for way in ways_to_color_H[:2]:
    print('H coloring:', way)
    colors_already = [-1 for _ in range(max_vertice+1)]
    colors_available = [set({1, 2, 3, 4}) for _ in range(max_vertice+1)]

    for i in range(7):
        colors_already[ Hs_start[i] ] = way[i]
        colors_available[ Hs_start[i] ] = {way[i]}
        colors_already, colors_available = process_just_colored_bfs(Hs_start[i], vertex_neigh, colors_already, colors_available, verbose=False)
    print(colors_available[:10])
    print('colors_available[412]:', colors_available[412])
    
    print('Started:', datetime.now())
    a = do_color(sorted_vertices, vertex_neigh, colors_already, colors_available, verbose=False)
    print('Finished:', datetime.now())
    
    assert(a == None)
    print()

