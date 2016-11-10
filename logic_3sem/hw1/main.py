file_in = open('task.in', 'r')
file_out = open('task.out', 'w', encoding='UTF-8')
import time

start_time = time.time()
s = ''
cur = 0

mod = 10 ** 9 + 7


class Tree:
	def get_hash(self):
		if self.hash == -1:
			if (self.right != 0):
				self.hash =  (self.key * self.left.get_hash() + self.key * self.right.get_hash() ** 2) % mod
			else:
				self.hash =  (self.key * self.left.get_hash()) % mod
		return self.hash

	def to_string(self):
		return (self.left.to_string() + self.char + self.right.to_string())

	def __eq__(self, other):
		if (type(self) != type(other)):
			return False
		return self.left == other.left and self.right == other.right


class Exp(Tree):
	key = 31
	char = '->'

	def __init__(self, left, right=0):
		self.left = left
		self.right = right
		self.hash = -1


class Disj(Tree):
	key =  37
	char = '|'

	def __init__(self, left, right=0):
		self.left = left
		self.right = right
		self.hash = -1


class Conj(Tree):
	key = 41
	char = '&'

	def __init__(self, left, right=0):
		self.left = left
		self.right = right
		self.hash = -1


class Neg:
	key = 43

	def __init__(self, exp):
		self.exp = exp
		self.hash = -1

	def __eq__(self, other):
		if (type(self) != type(other)):
			return False
		return self.exp == other.exp
	

	def get_hash(self):
		if self.hash == -1:
			self.hash = self.key * self.exp.get_hash() % mod
		return self.hash

	def to_string(self):
		return '!' + self.exp.to_string()


class Var:

	def __init__(self, name):
		self.name = name
		self.hash = -1

	def get_hash(self):
		if self.hash == -1:
			self.hash = hash(self.name) % mod
		return self.hash

	def to_string(self):
		return self.name

	def __eq__(self, other):
		if (type(self) != type(other)):
			return False
		return self.name == other.name

def parse(string):
	global s, cur
	s = string
	cur = 0
	return get_exp()


def get_exp():
	global s, cur
	obj = get_disj()
	if (cur < len(s) and s[cur] == '-'):
		cur += 1
		cur += 1
		obj = Exp(obj, get_exp())
	return obj


def get_disj():
	global s, cur
	obj = get_conj()
	while cur < len(s) and s[cur] == '|':
		cur += 1
		obj = Disj(obj, get_conj())
	return obj


def get_conj():
	global s, cur
	obj = get_neg()
	while cur < len(s) and s[cur] == '&':
		cur += 1
		obj = Conj(obj, get_neg())
	return obj


def get_name():
	global s, cur
	name = ''
	while cur < len(s) and s[cur] >= 'A' and s[cur] <= 'Z':
		name += s[cur]
		cur += 1
	return name


def get_neg():
	global s, cur
	if cur < len(s) and s[cur] == '!':
		cur += 1
		obj = get_neg()
		return Neg(obj)
	elif cur < len(s) and s[cur] >= 'A' and s[cur] <= 'Z':
		name = get_name() 
		return Var(name)
	else :
		cur += 1
		obj = get_exp()
		cur += 1
		return obj

axioms = [
		'A->B->A', 
		'(A->B)->(A->B->C)->(A->C)', 
		'A->B->A&B', 
		'A&B->A', 
		'A&B->B', 
		'A->A|B', 
		'B->A|B', 
		'(A->C)->(B->C)->(A|B->C)', 
		'(A->B)->(A->!B)->!A', 
		'!!A->A']


head = file_in.readline().replace(' ', '')
print(head,  end = '', file = file_out)
head = list(head.split(','))
statement = head[:-1] + head[-1].split('|-')
to_prove = statement.pop()

lines = []

for i in range(len(axioms)):
	# print(axioms[i])
	axioms[i] = parse(axioms[i])


saved = dict()
def is_axioms(exp):
	global saved
	for i in range(len(axioms)):
		saved.clear()
		if is_ax(exp, axioms[i]):
			return i + 1
	return 0


def is_ax(exp, ax):
	if isinstance(ax, Var):
		h = exp.get_hash()
		if not ax.name in saved.keys()	:
			saved[ax.name] = h 
		if saved[ax.name] == h:
			return True
	elif isinstance(ax, Neg):
		if isinstance(exp, Neg):
			return is_ax(exp.exp, ax.exp)
	elif type(ax) == type(exp):
		return is_ax(exp.left, ax.left) and is_ax(exp.right, ax.right)
	return False


st_flag = True
if (statement[0] == ''):
	st_flag = False

if st_flag:
	for i in range(len(statement)):
		statement[i] = parse(statement[i])


def is_statement(exp):
	if not st_flag:
		return 0
	for i in range(len(statement)):
		if statement[i].get_hash() == exp.get_hash() and statement[i] == exp:
			return i + 1
	return 0


def is_mp(exp):
	global n
	exp_hash = exp.get_hash()
	i = n - 1
	while i > 0:
		i -= 1
		if isinstance(lines[i], Exp) and lines[i].right.get_hash() == exp_hash:
			j = n - 1
			while j > 0:
				j -= 1
				if (lines[j].get_hash() == lines[i].left.get_hash()):
					return [j + 1, i + 1]
	return [0, 0]


n = 0
for line in file_in.readlines():
	if (line[-1] != '\n'):
		line += '\n'
	n += 1
	print('(', n, ') ', line[:-1], sep = '', end = '', file = file_out)
	line.replace(" ", "")
	line = parse(line)
	lines.append(line)

	ax_id = is_axioms(line)
	if ax_id != 0:
		print(' (Сх. акс. ', ax_id, ')', sep = '', file = file_out)
		continue

	st_id = is_statement(line)
	if st_id != 0:
		print(' (Предп. ', st_id, ')', sep = '', file = file_out)
		continue

	mp_id = is_mp(line)
	if (mp_id != [0, 0]):
		print(' (M.P. ', mp_id[0], ', ', mp_id[1], ')', sep = '', file = file_out)
		continue
	print (' Не доказано', file = file_out)


print(time.time() - start_time)
