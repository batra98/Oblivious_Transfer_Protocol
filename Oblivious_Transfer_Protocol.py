import random
from Crypto.Util import number
import gensafeprime
import numpy as np
import sympy as sp

rand = random.SystemRandom()



def generate_prime(n):
	if (n==2):
		p = 2
		g = 1
	elif (n==3):
	    p = 5
	    g = 2
	elif (n==4):
	    p = 11
	    g = 2
	elif (n==5):
	    p = 23
	    g = 11
	else:
		p = gensafeprime.generate(n)
		q = (p-1)//2

		t = 1
		while t == 1:
			h = number.getRandomRange(2,p-2)
			t = pow(h,2,p)

		g = h

	return (p,g)





class Alice_Client():
	def __init__(self,i):
		self.index = i
		self.b = 32

	def generate_rand_array(self,n,public_key):
		result = []
		self.random_ar = []

		for i in range(n):
			if i != self.index:
				r = rand.getrandbits(self.b)
			else:
				r = self.index


			self.random_ar.append(r)

			result.append(self.encrypt(public_key,r))

		return result





	def encrypt(self,public_key,r):
		h,p,g = public_key
		k = pow(g,rand.getrandbits(self.b),p)
		q = pow(g,k,p)
		s = pow(h,k,p)

		return (q,(r*s)%(p))


	def get_i_element(self,dec):

		result = []

		for i in range(len(dec)):
			result.append(dec[i] ^ self.random_ar[i])

		return result[self.index]






class Bob_Server():
	def __init__(self,data):
		self.data_array = data
		self.length = len(data)

	def generate_key(self,n):
		self.n = n
		self.p,self.g = generate_prime(n)
		self.x = number.getRandomRange(1,self.p-1)
		self.h = pow(self.g,self.x,self.p)

		public_key = (self.h,self.p,self.g)

		return public_key

	def decrypt(self,q,t):
		s = pow(q,self.x,self.p)
		s_inv = pow(s,self.p-2,self.p)

		return (t*s_inv)%(self.p)

	def decrypt_array(self,rndm_array):
		
		dec = []

		for i in range(len(rndm_array)):
			q,t = rndm_array[i]
			dec.append(self.decrypt(q,t) ^ self.data_array[i])

		return dec


def create_data(k,b,p):
	data = []
	for i in range(k):
		data.append(rand.getrandbits(b))

	return data


def create_blocks(n,data,p,k):

	blocks = []
	ids = []
	poly_value = 0
	for i in range(1,n+1,1):
		t = random.randint(1,n+1)
		while t in ids:
			t = random.randint(1,n+1)
		poly_value = 0
		for j in range(k):
			poly_value += ((data[j]%p)*(pow(t,j,p)%p))%p
		blocks.append(poly_value%p)
		ids.append(t)

	return (ids,blocks)

def reconstruct_coefficients(x,y,p,k):
	# M=np.ones(k*k).reshape((k,k))

	# for i in range(k):
	#     a=x[i]
	#     for j in range(1,k,1):
	#         M[i][j]=pow(a,j,p)

	# y=np.array(y)
	# # y=y[0:k]
	# M=np.linalg.inv(M)
	# M=np.dot(M,y)

	# coef=[]
	# for i in M:
	#     coef.append(int(round(i)))

	# print(coef)

	M = []

	for i in range(k):
		M.append([x[i],y[i]])

	M = np.array(M)
	x = np.tile(x,(k,1)).T
	t = np.tile(np.arange(k),(k,1))

	A = np.power(x,t)

	M = sp.Matrix(A).inv_mod(p) @ np.array(y)
	
	coef = []
	for i in M:
		coef.append(int(round(i))%p)



	return coef

def Hashing(x,y,k,g,p):
	# global g,p
	h = pow(g,x+k*y,p)
	return h

def Signing(ids,blocks,g,p):

	# global p,g

	encoded = []
	public_keys = []

	for i in range(len(blocks)):
		m = blocks[i]
		x = random.randrange(1,p,1) ##private key
		y = pow(g,x,p) ### public keys
		r = random.randrange(1,p,1)
		t = pow(g,r,p)
		c = Hashing(t,m,y,g,p)
		z = c*x+r

		encoded.append([ids[i],m,(t,z)])
		public_keys.append(y)

	return encoded,public_keys


def corrupt_blocks(n,encoded,e,b,p):

	# global p,b
	X = []
	for i in range(e):
		index = random.randrange(0,n,1)
		while index in X:
			index = random.randrange(0,n,1)

		X.append(index)

		m = rand.getrandbits(b)

		while m == encoded[index][1]:
			m = random.randrange(1,p,1)

		encoded[index][1] = m

	return encoded


def verify(y,z,t,m,g,p):
	# global p,g

	c = Hashing(t,m,y,g,p)
	X = pow(g,z,p)
	Y = ((pow(y,c,p))*(t%p))%p

	return X==Y


def verify_signature(public_keys,encoded,k,n,g,p):

	# global p,g

	recon_blocks = []

	if len(encoded) < k:
		print("Cannot recover data")

	for i in range(n):
		v = verify(public_keys[i],encoded[i][2][1],encoded[i][2][0],encoded[i][1],g,p)

		if v == True:
			recon_blocks.append(i)



	return recon_blocks



def Routing_Scheme(data = None):
	b = 257

	if data == None:
		k = 10
	else:
		k = len(data)
	e = 5
	n = k+e+1

	# p = gensafeprime.generate(256)
	p,g = generate_prime(b)

	if data == None:
		data = create_data(k,b,p)




	ids,blocks = create_blocks(n,data,p,k)

	encoded,public_keys = Signing(ids,blocks,g,p)

	# print(encoded)
	encoded = corrupt_blocks(n,encoded,e,b,p)
	# print(encoded)

	recon_blocks = verify_signature(public_keys,encoded,k,n,g,p)

	x = []
	y = []


	if(len(recon_blocks) < k):
		print("Cannot be recovered")
	else:
		j = 0
		for i in range(len(ids)):
			if j >= k:
				break 
			if i in recon_blocks:
				x.append(ids[i])
				y.append(blocks[i])
				j = j+1
		coef = reconstruct_coefficients(x,y,p,k)




	print("Data sent through channels:")
	print(data)
	print("Data received through channels:")
	print(coef)

	return coef


def Oblivious_Transfer():
	b = 128
	n = 12

	data = []
	for i in range(n):
		data.append(rand.getrandbits(b))

	index = number.getRandomRange(0,n-1)

	A = Alice_Client(index)
	B = Bob_Server(data)

	public = B.generate_key(b)

	rndm_array = A.generate_rand_array(n,public)

	# t = list(map(list, zip(*rndm_array))) ### can uncomment to see effect of routing but makes the programme considerably slow.

	# t[0] = Routing_Scheme(t[0]) ### can uncomment to see effect of routing but makes the programme considerably slow.
	# t[1] = Routing_Scheme(t[1]) ### can uncomment to see effect of routing but makes the programme considerably slow.
	
	# rndm_array=list(map(lambda x, y:(x,y), t[0], t[1])) ### can uncomment to see effect of routing but makes the programme considerably slow.


	dec = B.decrypt_array(rndm_array)
	# dec = Routing_Scheme(dec) ####can uncomment to see effect of routing but makes the programme considerably slow.
	
	ans = A.get_i_element(dec)


	print("Index = "+str(index))
	print("Data at index "+str(index)+" is "+str(data[index]))

	print("What A (Client) receives = "+str(ans))

	print(ans==data[index])



# Routing_Scheme()
Oblivious_Transfer()



