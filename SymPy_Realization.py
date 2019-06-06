
# coding: utf-8

# In[1]:


from sympy import *
import sys
from pprint import pprint
from datetime import datetime


# In[2]:


def neg(pt):
    return (-pt[0], -pt[1])


def shifted(pt, vec):
    return (pt[0] + vec[0], pt[1] + vec[1])


def rotated(pt, angle):
    return (pt[0] * cos(angle) - pt[1] * sin(angle), pt[0] * sin(angle) + pt[1] * cos(angle))


def rotatedabout(pt, origin, angle):
    return shifted(rotated(shifted(pt, neg(origin)), angle), origin)


def dist2(p, q):
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2


def simplified(pts):
    return {(p[0].simplify(), p[1].simplify()) for p in pts}


def factored(pts):
    return {(p[0].factor(), p[1].factor()) for p in pts}


def check_zero(x):
    if abs(x.evalf(2)) > 0.1:
        return False
    else:
        return x.equals(0)

    
def lez(x):
    v = x.evalf(2)
    if v < -0.1:
        return True
    elif v > 0.1:
        return False
    else:
        return x.simplify() <= 0

    
def get_edges_count(vertices):
    edges = []
    pts = sorted(vertices)
    fpts = [(p[0].evalf(2), p[1].evalf(2)) for p in pts]
    cnt = 0
    for i in range(len(pts)):
        sys.stdout.flush()
        l, r = -1, i
        while r > l + 1:
            m = (l + r) // 2
            if (fpts[i][0] - fpts[m][0]) > 1.1:
                l = m
            else:
                r = m
        for j in range(r, i):
            if abs(dist2(fpts[i], fpts[j]) - 1) < 0.01 and dist2(pts[i], pts[j]).equals(1):
                cnt += 1
                edges.append((pts[i], pts[j]))
    return cnt, edges


# ## Part 3

# ### Build H

# In[9]:


o = (Rational(0), Rational(0))
e = (Rational(1), Rational(0))


# In[10]:


def build_H():
    H = {o}
    for i in range(6):
        H.add(rotatedabout(e, o, pi / 3 * i))
    H = simplified(H)
    return H

H = build_H()
H_edges = get_edges_count(H)


# ### Build J

# In[11]:


def build_J():
    J = {o}
    for i in range(6):
        J.update( { rotated(shifted(x, shifted(e, rotated(e, pi / 3)) ), pi / 3 * i) for x in H } )
    return simplified(J)

J = build_J()
J_edges = get_edges_count(J)
print(len(J), 'vertices in J')
print(J_edges[0], 'edges in J')


# ### Build K

# In[12]:


def build_K():
    return ({rotated(x, -asin(Rational(1, 4))) for x in J}).union({rotated(x, asin(Rational(1, 4))) for x in J})


K = build_K()
K_edges = get_edges_count(K)

print(len(K), 'vertices in K')
print(K_edges[0], 'edges in K')


# ### Build L

# In[13]:


print('Started', datetime.now())

def build_L():
    a = neg(shifted(e, e))
    L = ({rotatedabout(x, a, -asin(Rational(1, 8))) for x in K})
    L = L.union({rotatedabout(x, a, asin(Rational(1, 8))) for x in K})
    return L

L = build_L()
L_edges = get_edges_count(L)
print('Finished', datetime.now())

print(len(L), 'vertices in L')
print(L_edges[0], 'edges in L')


# ## Part 4

# In[14]:


def build_T():
    tmp = {o, rotated(e, pi / 3), rotated(e, 2 * pi / 3), (0, sqrt(Integer(3)))}
    spindle = ({rotated(x, -asin(Rational(1, 2) / sqrt(3))) for x in tmp}).union({rotated(x, asin(Rational(1, 2) / sqrt(3))) for x in tmp})
    max_y = max(x[1] for x in spindle)
    py = min(spindle)
    qz = max(spindle)
    y = min(x for x in spindle if check_zero(x[1] - max_y))
    z = max(x for x in spindle if check_zero(x[1] - max_y))
    p = (2 * py[0] - y[0], y[1])
    q = (2 * qz[0] - z[0], z[1])
    spindle.update({p, q})
    return spindle

def build_U():
    T = build_T()
    vs = sorted(T, key=lambda x: x[1])
    a, b = vs[3:5]
    c = ((a[0] + b[0]) / 2, a[1] + abs(a[0] - b[0]) * sqrt(3) / 6)
    T = {shifted(x, neg(c)) for x in T}
    res = set()
    for i in range(3):
        res.update(simplified(rotated(x, 2 * pi * i / 3) for x in T))
    return res

def build_V():
    return simplified({rotated(rotated(e, pi * i / 3), j * asin(sqrt(Rational(1, 12)))) for i in range(6) for j in range(-2, 3)})

def build_W():
    V = build_V()
    return simplified({shifted(x, y) for x in V for y in V if lez(dist2(shifted(x, y), o) - 3)})


W = build_W()
print("W is built")
print(len(W), 'vertices in W')

