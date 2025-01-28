/-!
The Ackermann function is a classic example of a function that is not primitive recursive. It grows very quickly. But Lean's termination checker sees that it is terminating.
-/

/--
The Ackermann function is defined by recursion on two natural numbers. It grows very quickly.
-/
def ackermann : Nat → Nat → Nat
| 0, n => n+1
| m+1, 0 => ackermann m 1
| m+1, n+1 => ackermann m (ackermann (m+1) n)

#eval ackermann 4 0 -- 13
