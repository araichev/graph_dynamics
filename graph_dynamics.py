r"""
Python 2.7/Sage code for graph dynamics simulations.
Provide functionality to iteratively change the 
vertex colors of a given graph under various update rules.

Sage graph objects are used throughout.
For more about Sage Graph objects, see the 
``Sage graph theory documentation  <http://www.sagemath.org/doc/reference/sage/graphs/graph.html>``_.

In this code a *graph coloring* is an assignment of valid Sage color strings to the vertices of a graph.
So it is not a graph coloring in the standard graph theoretic sense of the term (``<https://en.wikipedia.org/wiki/Graph_coloring>``_), that is, our colorings do not require adjacent vertices to have different colors.
If you can think of a direct and less confusing term for us to use, please let us know.

CHANGELOG:

- Alex Raichev (AR), 2013-03-02: Initial version.
- AR, 2013-03-15: Added gsl() and created Rule class to improve interface.
- Mark C. Wilson (MCW), 2013-03-17: fixed GSL rule definition
- AR, 2013-03-22: Simplified functions and data structure for colorings. Added color() function to make coloring a graph easier. Used Counter objects to streamline code.

TODO:

- Add input type, output type, examples, and tests to docstrings.
- Implement methods that allow us to generate graphs and color them at the same time. E.g. attach a new node with probability proportional to the degree of existing nodes, and color it the same as that node with various probabilities, so that nodes of the same color are more likely to be neighbors.
- Add unit tests (as a separate file).

"""
#*****************************************************************************
#       Copyright (C) 2013 Alexander Raichev <alex.raichev@gmail.com>
#
#  Distributed under the terms of the GNU Lesser General Public License (LGPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

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
    
def color(graph, color_list=[], pad_randomly=[]):
    r"""
    Assign ``graph.vertices()`` the colors in ``color_list`` in order and 
    return the resulting coloring.
    If there are any vertices uncolored because ``color_list`` is too short,
    then color each such vertex with one of the colors drawn uniformly at
    random from the list of colors in ``pad_randomly``.
    """
    coloring = dict()
    k = len(color_list)
    if k > 0:
        # Color graph according to color_list
        for i in range(k):
            coloring[graph.vertices()[i]] = color_list[i]
    if k < graph.num_verts() and pad_randomly:
        # Color rest of graph according to pad_randomly.
        num_colors = len(pad_randomly)
        for x in graph.vertices()[k:]:
            color = pad_randomly[randint(0, num_colors - 1)]
            coloring[x] = color
    return coloring

# Color update rules.
def majority(graph, coloring):
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

def plurality(graph, coloring):
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

def gsl3(graph, coloring, color_palette=['green', 'red', 'yellow'],
         T=0.5, t=0.25, s=0.25):
    r"""
    Update the coloring of the given graph via the 
    Girard-Seligman-Liu (GSL) 3-color rule.
    Assume ``color_palette`` has at least 3 colors,
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
    new_coloring = dict()
    green = color_palette[0]
    red = color_palette[1]
    yellow = color_palette[2]
    # Update the colors of G's vertices.
    for x in G.vertices():
        nb_color_count = Counter() #{green: 0, red: 0, yellow: 0}
        for y in G.neighbors(x):
            color = coloring[y]
            if color in {green, red, yellow}:
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

def gsl2(graph, coloring, color_palette=['green', 'yellow'],
         T=0.5):
    r"""
    Update the coloring of the given graph via the 
    Girard-Seligman-Liu (GSL) 2-color rule.
    Assume ``color_palette`` has at least 2 colors,
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

RULES = ['majority', 'plurality', 'gsl3', 'gsl2']


class Rule(object):
    r"""
    Wrapper for a graph update rule.
    A callable (function-like) object.
    
    INSTANCE ATTRIBUTES:
    
    - ``name`` - The name (string) of an existing update rule. 
    - ``kwargs`` - (Optional; default = {}) Keyword arguments (dictionary) 
      needed for the update rule's definition.  For example, 
      this could be {'T': 0.99, 's': 0.3, 't': 0.3} in case of the GSL3 rule.
    """
    def __init__(self, name, **kwargs):
        if name not in RULES:
            print 'Oops! Rule must be one of', RULES
            return
        self.name = name
        self.kwargs = kwargs
    
    def __str__(self):
        result = ['Rule:']
        result.append('    name: ' + str(self.name))
        result.append('    kwargs: ' + str(self.kwargs))
        return "\n".join(result)   
    
    def __call__(self, graph, coloring):
        f = globals()[self.name]
        return f(graph, coloring, **self.kwargs)
    
def iterate(graph, coloring, rule, num_steps=10):
    r"""
    Return the sequence  [c_0, c_1, ..., c_n] of colorings of the
    given graph, where c_0 = ``coloring``, c_{i+1} for i > 0 is ``rule(c_i)``, 
    and n is the max of ``num_steps`` and the number of steps it takes for the 
    colorings to stabilize.
    """
    result = [coloring]
    for i in range(num_steps):
        c_old = result[-1]
        c_new = rule(graph, c_old)
        if c_old == c_new:
            # Stabilized
            break
        result.append(c_new)
    return result

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
        print "Step", i
        graph.show(pos=pos, vertex_colors=invert_dict(c), 
               vertex_labels=vertex_labels, figsize=figsize)