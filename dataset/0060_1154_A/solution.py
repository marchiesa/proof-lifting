lst = list(map(int, input().split()))
max_value = max(lst)

result = []

for element in lst:
	if element != max_value:
		result.append(max_value - element)

print(*result)