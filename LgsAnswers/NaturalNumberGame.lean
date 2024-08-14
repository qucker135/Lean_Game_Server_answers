import Mathlib

-- Tutorial World

example (x q : ℕ) : 37 * x + q = 37 * x + q := by
  rfl

example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]

example : 2 = succ (succ 0) := by
  rw [← one_eq_succ_zero, ← two_eq_succ_one]
  rfl

example : 2 = succ (succ 0) := by
  rw [← one_eq_succ_zero, ← two_eq_succ_one]
  rfl

example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero, add_zero]
  rfl

example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero c, add_zero]
  rfl

theorem succ_eq_add_one n : succ n = n + 1 := by
  rw [one_eq_succ_zero, add_succ, add_zero]
  rfl

example : (2 : ℕ) + 2 = 4 := by
  nth_rewrite 2 [two_eq_succ_one]
  rw [one_eq_succ_zero]
  repeat rw [add_succ]
  rw [add_zero, ← three_eq_succ_two, ← four_eq_succ_three]
  rfl

-- Addition World

theorem zero_add (n : ℕ) : 0 + n = n := by
  induction n with d hd
  rw [add_zero]
  rfl
  rw [add_succ, hd]
  rfl

theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  induction b with d hd
  repeat rw [add_zero]
  rfl
  repeat rw [add_succ]
  rw [hd]
  rfl

theorem add_comm (a b : ℕ) : a + b = b + a := by
  induction b with d hd
  rw [add_zero, zero_add]
  rfl
  rw [add_succ, succ_add, hd]
  rfl

theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction c with d hd
  repeat rw [add_zero]
  rfl
  repeat rw [add_succ]
  rw [hd]
  rfl

theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b, add_assoc]
  rfl

-- Multiplication World

theorem mul_one (m : ℕ) : m * 1 = m := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]
  rfl

theorem zero_mul (m : ℕ) : 0 * m = 0 := by
  induction m with d hd
  rw [mul_zero]
  rfl
  rw [mul_succ, hd, add_zero]
  rfl

theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  induction b with d hd
  repeat rw [mul_zero]
  rw [add_zero]
  rfl
  repeat rw [mul_succ]
  rw [hd]
  repeat rw [add_assoc]
  repeat rw [add_succ]
  rw [add_comm d a]
  rfl

theorem mul_comm (a b : ℕ) : a * b = b * a := by
  induction b with d hd
  rw [mul_zero, zero_mul]
  rfl
  rw [mul_succ, succ_mul, hd]
  rfl

theorem one_mul (m : ℕ): 1 * m = m := by
  rw [mul_comm, mul_one]
  rfl

theorem two_mul (m : ℕ): 2 * m = m + m := by
  rw [two_eq_succ_one, succ_mul, one_mul]
  rfl

theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction c with d hd
  rw [add_zero, mul_zero, add_zero]
  rfl
  rw [add_succ, mul_succ, mul_succ, hd, add_assoc]
  rfl

theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  repeat rw [mul_comm _ c]
  rw [mul_add]
  rfl

theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  induction c with d hd
  repeat rw [mul_zero]
  rfl
  repeat rw [mul_succ]
  rw [mul_add, hd]
  rfl

-- Implication World

example (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  exact h1

example (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  repeat rw [zero_add] at h
  exact h

example (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  apply h2 at h1
  exact h1

example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  rw [four_eq_succ_three, one_eq_succ_zero, add_succ, add_zero] at h
  apply succ_inj at h
  exact h

example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  rw [four_eq_succ_three, one_eq_succ_zero, add_succ, add_zero] at h
  apply succ_inj
  exact h

example (x : ℕ) : x = 37 → x = 37 := by
  intro h
  exact h

example (x : ℕ) : x + 1 = y + 1 → x = y := by
  intro h
  repeat rw [← succ_eq_add_one] at h
  apply succ_inj
  exact h

example (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  apply h2 at h1
  exact h1

theorem zero_ne_one : (0 : ℕ) ≠ 1 := by
  intro h
  rw [one_eq_succ_zero] at h
  apply zero_ne_succ at h
  exact h

theorem one_ne_zero : (1 : ℕ) ≠ 0 := by
  symm
  apply zero_ne_one

example : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  intro h
  repeat rw [add_succ] at h
  rw [add_zero] at h
  repeat apply succ_inj at h
  apply zero_ne_succ at h
  exact h

-- Power World

theorem zero_pow_zero : (0 : ℕ) ^ 0 = 1 := by -- d'oh!
  rw [pow_zero]
  rfl

theorem zero_pow_succ (m : ℕ) : (0 : ℕ) ^ (succ m) = 0 := by
  induction m with d hd
  rw [pow_succ, pow_zero, mul_zero]
  rfl
  rw [pow_succ, mul_zero]
  rfl

theorem pow_one (a : ℕ) : a ^ 1 = a := by
  rw [one_eq_succ_zero, pow_succ, pow_zero, one_mul]
  rfl

theorem one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  induction m with d hd
  rw [pow_zero]
  rfl
  rw [pow_succ, hd, mul_one]
  rfl

theorem pow_two (a : ℕ) : a ^ 2 = a * a := by
  rw [two_eq_succ_one, pow_succ, pow_one]
  rfl

theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with n hn
  rw [add_zero, pow_zero, mul_one]
  rfl
  rw [add_succ, pow_succ, pow_succ, hn, mul_assoc]
  rfl

theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with n hn
  repeat rw [pow_zero]
  rw [mul_one]
  rfl
  repeat rw [pow_succ]
  rw [hn]
  rw [mul_assoc, ← mul_assoc (b^n), mul_comm (b^n), mul_assoc a, ←   mul_assoc]
  rfl

theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with n hn
  rw [pow_zero, mul_zero, pow_zero]
  rfl
  rw [pow_succ, mul_succ, pow_add, hn]
  rfl

theorem add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  repeat rw [pow_two]
  rw [mul_assoc, two_mul]
  rw [mul_add, add_mul, add_mul, mul_comm b a]
  rw [add_assoc, add_comm (a*b), add_comm (a*b), add_assoc (b*b), ←   add_assoc]
  rfl

example (a b c n : ℕ) : (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := by
  sorry -- I've found a solution, but it's too long to fit here.

-- Advanced Addition World

theorem add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  intro h
  induction n with n hn
  repeat rw [add_zero] at h
  exact h
  repeat rw [add_succ] at h
  apply succ_inj at h
  apply hn at h
  exact h

theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  intro h
  repeat rw [add_comm n] at h
  apply add_right_cancel at h
  exact h

theorem add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by
  intro h
  induction y with y hy
  rw [add_zero] at h
  exact h
  rw [add_succ] at h
  apply succ_inj at h
  apply hy at h
  exact h

theorem add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  intro h
  rw [add_comm] at h
  apply add_left_eq_self at h
  exact h

theorem add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  cases b with d
  rw [add_zero]
  intro h
  exact h
  rw [add_succ]
  intro h
  symm at h
  apply zero_ne_succ at h
  cases h

theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  rw [add_comm]
  intro h
  apply add_right_eq_zero at h
  exact h

-- Algorithm World

theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [add_comm, add_assoc, add_comm c]
  rfl

example (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  repeat rw [add_assoc]
  rw [add_left_comm b c, add_comm b d]
  rfl

example (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_assoc, add_left_comm, add_comm]

example (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp_add

example (a b : ℕ) (h : succ a = succ b) : a = b := by
  rw [← pred_succ a, h, pred_succ]
  rfl

theorem succ_ne_zero (a : ℕ) : succ a ≠ 0 := by
  intro h
  rw [← is_zero_succ a, h, is_zero_zero]
  cases h

theorem succ_ne_succ (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  contrapose! h
  apply succ_inj m n
  exact h

example : (20 : ℕ) + 20 = 40 := by
  decide

example : (2 : ℕ) + 2 ≠ 5 := by
  decide

-- ≤ World

theorem le_refl (x : ℕ) : x ≤ x := by
  use 0
  rw [add_zero]
  rfl

theorem zero_le (x : ℕ) : 0 ≤ x := by
  use x
  rw [zero_add]
  rfl

theorem le_succ_self (x : ℕ) : x ≤ succ x := by
  use 1
  rw [succ_eq_add_one]
  rfl

theorem le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  cases hxy with a ha
  cases hyz with b hb
  use (a+b)
  rw [hb, ha, add_assoc]
  rfl

theorem le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  cases hx with d hd
  symm at hd
  apply add_right_eq_zero at hd
  exact hd

theorem le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  cases hxy with a ha
  cases hyx with b hb
  rw [ha, add_assoc] at hb
  nth_rewrite 1 [← add_zero x] at hb
  apply add_left_cancel at hb
  symm at hb
  apply add_right_eq_zero at hb
  rw [hb, add_zero] at ha
  symm at ha
  exact ha

example (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  cases h with h1 h2
  right
  exact h1
  left
  exact h2

theorem le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  induction x with a ha
  left
  apply zero_le
  cases ha with hb hc
  cases hb with w
  cases w with d
  rw [add_zero] at h
  right
  rw [h]
  apply le_succ_self
  left
  use d
  rw [add_succ] at h
  rw [succ_add]
  exact h
  right
  cases hc
  use (succ w)
  rw [h, add_succ]
  rfl

theorem succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  cases hx with w hw
  use w
  rw [succ_add] at hw
  apply succ_inj
  exact hw

theorem le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  cases hx with w hw
  cases x with a ha
  left
  rfl
  rw [one_eq_succ_zero, succ_add] at hw
  apply succ_inj at hw
  symm at hw
  apply add_right_eq_zero at hw
  right
  rw [hw, one_eq_succ_zero]
  rfl

theorem le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  cases hx with w hw
  cases x with a ha
  left
  rfl
  rw [two_eq_succ_one, succ_add] at hw
  apply succ_inj at hw
  right
  cases a with b hb
  left
  rw [one_eq_succ_zero]
  rfl
  rw [one_eq_succ_zero, succ_add] at hw
  apply succ_inj at hw
  symm at hw
  apply add_right_eq_zero at hw
  right
  rw [hw]
  rw [two_eq_succ_one, one_eq_succ_zero]
  rfl

-- Advanced Multiplication World

theorem mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  cases h with w hw
  use (w*t)
  rw [hw, add_mul]
  rfl

theorem mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  contrapose! h
  rw [h, mul_zero]
  rfl

theorem eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
  cases a with d hd
  tauto
  use d
  rfl

theorem one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  cases a with b hb
  tauto
  use b
  rw [add_comm, succ_eq_add_one]
  rfl

theorem le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  induction b with b hb
  rw [mul_zero] at h
  tauto
  rw [mul_succ]
  use (a*b)
  rw [add_comm]
  rfl

theorem mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  have h2 : x * y ≠ 0 := by
    rw [h]
    tauto
  apply le_mul_right at h2
  rw [h] at h2
  cases h2 with w hw
  cases w
  rw [add_zero] at hw
  symm
  exact hw
  rw [one_eq_succ_zero, add_succ] at hw
  apply succ_inj at hw
  symm at hw
  apply add_right_eq_zero at hw
  rw [hw, zero_mul] at h
  tauto

theorem mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  cases a with a ha
  tauto
  cases b with b hb
  tauto
  rw [mul_succ, add_succ]
  symm
  apply zero_ne_succ

theorem mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  contrapose! h
  apply mul_ne_zero
  tauto
  tauto

theorem mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  induction b with d hd generalizing c
  rw [mul_zero] at h
  symm at h
  apply mul_eq_zero at h
  cases h with h1 h2
  tauto
  symm
  exact h2
  cases c with e
  rw [mul_zero] at h
  apply mul_eq_zero at h
  cases h with h1 h2
  tauto
  exact h2
  repeat rw [mul_succ] at h
  apply add_right_cancel at h
  apply hd at h
  rw [h]
  rfl

theorem mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  induction b with w hw
  rw [mul_zero] at h
  tauto
  rw [mul_succ] at h
  nth_rewrite 3 [← zero_add a] at h
  apply add_right_cancel at h
  apply mul_eq_zero at h
  cases h with h1 h2
  tauto
  rw [h2, one_eq_succ_zero]
  rfl
