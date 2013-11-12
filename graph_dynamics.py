r"""
Python 2.7/Sage code for running graph dynamics simulations.
Provide functionality to iteratively change the 
vertex colors of a given graph under various update rules.

Sage graph objects are used throughout.
For more about Sage Graph objects, see the 
`Sage graph theory documentation  <http://www.sagemath.org/doc/reference/sage/graphs/graph.html>`_.

In this code a *graph coloring* is an assignment of valid Sage color strings to the vertices of a graph.
So it is not a graph coloring in the standard graph theoretic sense of the term (``<https://en.wikipedia.org/wiki/Graph_coloring>``_), that is, our colorings do not require adjacent vertices to have different colors.
If you can think of a direct and less confusing term for us to use, please let us know.

CHANGELOG:

- Alex Raichev (AR), 2013-03-02: Initial version.
- AR, 2013-03-15: Added gsl() and created Rule class to improve interface.
- Mark C. Wilson (MCW), 2013-03-17: fixed GSL rule definition
- AR, 2013-03-22: Simplified functions and data structure for colorings. 
  Added color() function to make coloring a graph easier. 
  Used Counter objects to streamline code.
- AR, 2013-11-11: Simplified functions and cleaned up GSL rules. 
  Added get_stats().

TODO:

- Add input type, output type, examples, and tests to docstrings.
- Implement methods that allow us to generate graphs and color them at the
  same time. E.g. attach a new node with probability proportional to the 
  degree of existing nodes, and color it the same as that node with various 
  probabilities, so that nodes of the same color are more likely to be 
  neighbors.
- Add unit tests (as a separate file).

"""
#*****************************************************************************
#       Copyright (C) 2013 Alexander Raichev <alex.raichev@gmail.com>
#
#  Distributed under the terms of the GNU Lesser General Public License (LGPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from __future__ import division, print_function
from random import randint
from collections import Counter
        
r"""
Store a graph coloring as a dictionary, where the keys are the vertices of the graph (Sage Graph object), and the corresponding values are valid Sage color specifiers (such as 'green' or (0.2, 0.8, 0.1)) indicating the colors of the vertices.
"""
        
def invert_dict(coloring):
    r"""
    Invert the given graph coloring.
    That is, return a dictionary, where each key is a valid Sage color 
    and each corresponding value is the set of vertices of that color.
    Sage's show() command requires colorings in this format.
    """
    d = dict()
    for x in coloring.keys():
        color = coloring[x] 
        d[color] = d.get(color, set())
        d[color].add(x)
    return d
    
def color_count(coloring):
    r"""
    Return a counter of the the colors in the given coloring.
    """
    from collections import Counter
    return Counter(coloring.values())

def color(graph, color_list=[]):
    r"""
    Return a coloring of the given graph based on the given color list by
    assigning ``graph.vertices()`` the colors in ``color_list`` in order.
    So the first vertex of the graph is assigned the first color in the color
    list, the second vertex the second color, and so on.
    """
    k = len(color_list)
    n = graph.num_verts()
    assert k == n,\
      "The color list must be of length %s, the number of vertices in %s" % (n, graph)

    coloring = dict()
    for i in range(n):
        coloring[graph.vertices()[i]] = color_list[i]
    return coloring

# Coloring functions.
def color_randomly(graph, color_palette=[]):
    r"""
    Return a random coloring of the given graph based on the given color
    palette.
    Specifically, for each vertex in the graph, assign it one of the colors
    in the color palette chosen uniformly at random.
    """
    k = len(color_palette)
    assert k > 0,\
      "The color palette must contain at least one color"

    coloring = dict()
    for v in graph.vertices():
        coloring[v] = color_palette[randint(0, k - 1)]
    return coloring

# Color update rules.
def majority_rule(graph, coloring):
    r"""
    Update the coloring of the given graph according to the majority rule.
    Under this rule, a vertex x becomes the color that occurs 
    in the majority (> 0.5) of its neighbors.
    If a majority color does not exist, then x does not change color.
    """
    G = graph
    new_coloring = dict()
    # Update the colors of G's vertices and store them in H
    for x in G.vertices():
        # Find majority color of x's neighbors.
        nb_color_count = Counter()
        for y in G.neighbors(x):
            color = coloring[y]
            nb_color_count[color] += 1
        max_color, max_count = nb_color_count.most_common(1)[0]
        num_neighbors = sum(nb_color_count.values())
        # Color x the majority color if it exists.
        if max_count > 0.5*num_neighbors:
            new_coloring[x] = max_color
        else:
            # Keep x's old color.
            new_coloring[x] = coloring[x]
    return new_coloring

def plurality_rule(graph, coloring):
    r"""
    Update the coloring of the given graph via the plurality rule.
    Under this rule, a vertex x becomes the color that occurs most
    among its neighbors.
    If the maximum color frequency is 1, then x does not change color.
    """
    G = graph
    new_coloring = dict()
    # Update the colors of G's vertices and store them in H
    for x in G.vertices():
        # Find plurality color of x's neighbors.
        nb_color_count = Counter()
        for y in G.neighbors(x):
            color = coloring[y]
            nb_color_count[color] += 1
        max_color, max_count = nb_color_count.most_common(1)[0]
        # Color x the plurality color, if it exists.
        if max_count > 1:
            new_coloring[x] = max_color
        else:
            # Keep x's old color.
            new_coloring[x] = coloring[x]
    return new_coloring

def gsl2_rule(graph, coloring, color_palette=['green', 'yellow'],
         T=0.5):
    r"""
    Update the coloring of the given graph via the 
    Girard-Seligman-Liu (GSL) 2-color rule.
    Assume ``color_palette`` has exactly 2 colors,
    which we will interpret as 
      green = ``color_palette[0]`` (for a proposition) and
      yellow = ``color_palette[1]`` (undecided) 
    in the Girard-Seligman-Liu terminology.

    NOTES:

    The GSL2 rule is this.
    For each vertex x in the graph, do the following.
    If green makes up more than a fraction T of x's neighbors,
    then color x green.
    Otherwise, don't change x's color. 
    """ 
    G = graph
    assert len(set(color_palette)) == 2,\
      "color_palette must contain exactly 2 different colors"

    new_coloring = dict()
    green = color_palette[0]
    yellow = color_palette[1]
    # Update the colors of G's vertices.
    for x in G.vertices():
        nb_color_count = Counter() #{green: 0, yellow: 0}
        for y in G.neighbors(x):
            color = coloring[y]
            if color in {green, yellow}:
                nb_color_count[color] += 1
        num_neighbors = sum(nb_color_count.values())   
        x_color = coloring[x]
        # Check for strong influence. 
        if nb_color_count[green] > T*num_neighbors: 
            new_coloring[x] = green 
        # No influence. 
        else:
            new_coloring[x] = x_color
    return new_coloring

def gsl3_rule(graph, coloring, color_palette=['green', 'red', 'yellow'],
         T=0.5, t=0.25, s=0.25):
    r"""
    Update the coloring of the given graph via the 
    Girard-Seligman-Liu (GSL) 3-color rule.
    Assume ``color_palette`` has exactly 3 different colors,
    which we will interpret as 
      green = ``color_palette[0]`` (for a proposition), 
      red = ``color_palette[1]`` (against a proposition), and
      yellow = ``color_palette[2]`` (undecided) 
    in the Girard-Seligman-Liu terminology.
    Assume the following relations hold for the given parameters: 
    ``T >= 0.5`` and ``s + t <= T``.

    NOTES:

    The GSL3 rule is this.
    For each vertex x in the graph, do the following.
    Check for strong influence:
    If green or red makes up more than a fraction T of x's neighbors,
    then color x green or red, respectively.
    Otherwise, check for weak influence:
    If x is green or red and has less than a fraction t
    of green or red neighbors, respectively, and 
    has at least a fraction s of red or green neighbors, respectively,
    then color x yellow.
    Otherwise, don't change x's color. 
    """ 
    G = graph
    assert len(set(color_palette)) == 3,\
      "color_palette must contain exactly 3 different colors"

    green = color_palette[0]
    red = color_palette[1]
    yellow = color_palette[2]
    # Update the colors of G's vertices.
    new_coloring = dict()
    for x in G.vertices():
        nb_color_count = Counter() #{green: 0, red: 0, yellow: 0}
        for y in G.neighbors(x):
            color = coloring[y]
            nb_color_count[color] += 1
        num_neighbors = sum(nb_color_count.values())   
        x_color = coloring[x]
        # Check for strong influence. 
        if nb_color_count[green] > T*num_neighbors: 
            new_coloring[x] = green 
        elif nb_color_count[red] > T*num_neighbors: 
            new_coloring[x] = red 
        # Check for weak influence. 
        elif (x_color == green and\
          nb_color_count[green] < t*num_neighbors and\
          nb_color_count[red] >= s*num_neighbors):
            new_coloring[x] = yellow
        elif (x_color == red and\
          nb_color_count[red] < t*num_neighbors and\
          nb_color_count[green] >= s*num_neighbors):
            new_coloring[x] = yellow
        # No influence. 
        else:
            new_coloring[x] = x_color
    return new_coloring
    
def iterate(update_rule, update_rule_kwargs, graph, initial_coloring, 
  num_steps=10):
    r"""
    Return the pair (s, stabilized), where s is the sequence  
    [c_0, c_1, ..., c_n] of colorings of the
    given graph, where c_0 = ``inital_coloring``, c_{i+1} for i > 0 is 
    ``update_rule(graph, c_i, **update_rule_kwargs)``, 
    and n is the max of ``num_steps`` and the number of steps it takes for the 
    colorings to stabilize, and where stabilized is ``True`` if the colorings
    stabilized and ``False`` otherwise.
    """
    s = [initial_coloring]
    stabilized = False
    for i in range(num_steps):
        c_old = s[-1]
        c_new = update_rule(graph, c_old, **update_rule_kwargs)
        if c_old == c_new:
            # Stabilized
            stabilized = True
            break
        s.append(c_new)
    return s, stabilized

def show_colorings(graph, colorings, pos=None, vertex_labels=False, figsize=3):
    r"""
    Draw all the colorings of the given graph that are listed in ``colorings``.
    Position the vertices according to the coordinates in ``pos``.
    Label the vertices iff ``vertex_labels== True``.
    Set the size of each graph via ``figsize``.   
    """
    if pos is None:
        pos = graph.layout()
    for (i, c) in enumerate(colorings):
        print("Step", i)
        graph.show(pos=pos, vertex_colors=invert_dict(c), 
               vertex_labels=vertex_labels, figsize=figsize)

def get_stats(update_rule, update_rule_kwargs, 
  graph_generator, graph_generator_kwargs,
  coloring_function, coloring_function_kwargs, 
  num_steps=10, num_runs=1000, print_stats=True):
    r"""
    For i in ``range(num_runs)``, run 
    ``iterate(update_rule, update_rule_kwargs, G_i, c_i, 
    num_steps=num_steps)``,
    where G_i is the graph generated by 
    ``graph_generator(**graph_generator_kwargs)`` on the ith run, and c_i is
    the initial coloring generated by 
    ``coloring_function(G_i, **coloring_function_kwargs)`` on the ith run.

    For each run that stabilizes, save the initial and final colorings.
    After all runs calculate and return the following stats below in order:

    - The number of runs that stabilized within ``num_steps`` steps
    - The (sample) mean number of steps required to stabilize over all runs 
    that stabilized
    - The mean color counts of the initial colorings over all runs
    that stabilized
    - The mean color counts of the final colorings over all runs
    that stabilized

    If ``print_stats == True``, then pretty print the stats as well.
    """
    from collections import Counter 

    ur = update_rule
    urk = update_rule_kwargs
    gg = graph_generator
    ggk = graph_generator_kwargs
    cf = coloring_function
    cfk = coloring_function_kwargs
    step_counts = []
    initial_color_counts = []
    final_color_counts = []
    for i in range(num_runs):
        G = gg(**ggk)
        ic = cf(G, **cfk)
        s, stabilized = iterate(ur, urk, G, ic)
        if stabilized:
            initial_color_counts.append(color_count(s[0]))
            final_color_counts.append(color_count(s[-1]))
            step_counts.append(len(s))

    N = len(step_counts)
    if not N:
        return N, None, None, None
    mean_steps = sum(step_counts)/N
    mean_initial_color_count = Counter({color: sum(c[color] 
      for c in initial_color_counts)/N for color in color_palette}) 

    mean_final_color_count =  Counter({color: sum(c[color] 
      for c in final_color_counts)/N for color in color_palette})

    if print_stats:
        # Print stats and round to 3 significant figures
        print(ur)
        print(gg)
        print(cf)
        print('-'*20)
        print('Number of runs: {!s}'.format(num_runs))
        print('Number of runs that stabilized: {!s}'.format(N))
        print('Mean number of steps required to stabilize: {:.3g}'.format(
          mean_steps))
        print('Mean initial color counts:')
        for color, mean in sorted(mean_initial_color_count.items()):
            print('    {!s}: {:.3g}'.format(color, mean))
        print('Mean finial color counts:')
        for color, mean in sorted(mean_final_color_count.items()):
            print('    {!s}: {:.3g}'.format(color, mean))
        
    return (
      N,
      mean_steps,
      mean_initial_color_count,
      mean_final_color_count,
    )