### TEAM MEMBERS
## MEMBER 1: 210050012
## MEMBER 2: 210050086
## MEMBER 3: 210050104


from z3 import *
import sys
from itertools import *

file = sys.argv[1]

with open(file) as f:
	n,t = [int(x) for x in next(f).split()]
	matrix = []
	for line in f:
		matrix.append([int(x) for x in line.split()])
		

def solve(T):
	if T == 0:
		return [unsat, []]

	s=Solver()

	a = []
	for i in range(n):
		a+=[[]]
		for j in range(n):
			a[i] += [[]]
			for t in range(T+1):
				a[i][j] += [Int("x_%i_%i_%i" % (i,j,t))]
		

	for i in range(n):
		for j in range(n):
			a[i][j][0] = matrix[i][j]

	r = []
	u = []
	l = []
	d = []
	for i in range(n):
		r += [[]]
		u += [[]]
		l += [[]]
		d += [[]]
		for j in range(T):
			r[i] += [Bool("r_%i_%i" % (i,j))]
			u[i] += [Bool("u_%i_%i" % (i,j))]
			l[i] += [Bool("l_%i_%i" % (i,j))]
			d[i] += [Bool("d_%i_%i" % (i,j))]
	

	def final(t):
		f = []
		for i in range(n):
			for j in range(n):
				f.append(a[i][j][t] == (n*i+j+1))
		return And(f)	

	def nope(t):
		f = []
		for i in range(n):
			for t1 in range(t+1, T):
				f.append(Not(r[i][t1]))
				f.append(Not(l[i][t1]))
				f.append(Not(u[i][t1]))
				f.append(Not(d[i][t1]))
		return And(f)

	s.add(final(T))


	for t in range(T):
		s.add(Implies(final(t), And(final(t+1),nope(t))))
		for i in range(n):
			right = []
			for j in range(n):
				right.append(a[i][j][t+1]==a[i][(j-1)%n][t])
				for k in range(n):
					if k != i:
						right.append(a[k][j][t+1]==a[k][j][t])
			right_cond = And(right)
			s.add(Implies(r[i][t], right_cond))
			left = []
			for j in range(n):
				left.append(a[i][j][t+1]==a[i][(j+1)%n][t])
				for k in range(n):
					if k != i:
						left.append(a[k][j][t+1]==a[k][j][t])
			left_cond = And(left)
			s.add(Implies(l[i][t], left_cond))
			up = []
			for j in range(n):
				up.append(a[j][i][t+1]==a[(j+1)%n][i][t])
				for k in range(n):
					if k != i:
						up.append(a[j][k][t+1]==a[j][k][t])
			up_cond = And(up)
			s.add(Implies(u[i][t], up_cond))
			down = []
			for j in range(n):
				down.append(a[j][i][t+1]==a[(j-1)%n][i][t])
				for k in range(n):
					if k != i:
						down.append(a[j][k][t+1]==a[j][k][t])
			down_cond = And(down)
			s.add(Implies(d[i][t], down_cond))

	for i in range(T):
		new1=[]
		for j in range(n):
				new1.append(r[j][i])
				new1.append(l[j][i])
				new1.append(d[j][i])
				new1.append(u[j][i])
		exactly_one_true = Sum([If(var, 1, 0) for var in new1]) == 1
		s.append(exactly_one_true) 
	if s.check() == unsat:
		return solve(T-1)
	else:
		moves = []
		m = s.model()
		for i in range(T):
			for j in range(n):
				if is_true(m[r[j][i]]):
					p = str(j)
					p1 = p+"r"
					moves.append(p1)
				if is_true(m[l[j][i]]):
					p = str(j)
					p1 = p+"l"
					moves.append(p1)
				if is_true(m[d[j][i]]):
					p = str(j)
					p1 = p+"d"
					moves.append(p1)
				if is_true(m[u[j][i]]):
					p = str(j)
					p1 = p+"u"
					moves.append(p1)
		return [sat,moves]
	
[s,m] = solve(t)
print(s)
for i in m:
	print(i)