value=dict() # a rough score assigned to each prime to determine the optimal path

# primes below 1000 are assigned 1
# above that, recursively calculate the value of each prime factor of n-1
# and then among all the divisors that are roughly above n^(1/3),
# sum over the values of all the prime factors
# and find the minimum
def find_value(n):
	global value
	if n < 1000: return 1
	if n in value: return value[n][0]
	fact = factor(n-1)
	res = optimise(n,fact) # returns (min_value, chosen_factors)
	value[n] = res
	return res[0]

def optimise(n,fact):

n=int(input("Please input a prime number to be certified:"))
print("Number received: n=%d"%n)
if not n in Primes():
	print("It is not prime.")
	sys.exit()
