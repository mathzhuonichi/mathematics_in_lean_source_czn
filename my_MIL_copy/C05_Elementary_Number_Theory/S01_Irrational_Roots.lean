import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime

#print Nat.coprime

example (m n : Nat) (h : m.coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.coprime n) : m.gcd n = 1 := by
  rw [Nat.coprime] at h
  exact h

example : Nat.coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    -- sorry
    apply Nat.Prime.dvd_of_dvd_pow
    trivial
    rw[sqr_eq]
    norm_num
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 :=by
    -- sorry
    -- (mul_right_inj' (by norm_num)).mp this
    rw[mul_right_inj'] at this
    assumption
    norm_num
  have : 2 ∣ n := by
    -- sorry
    apply Nat.Prime.dvd_of_dvd_pow
    norm_num
    rw[←this]
    norm_num
  have : 2 ∣ m.gcd n := by
    -- sorry
    apply Nat.dvd_gcd
    trivial
    trivial
  have : 2 ∣ 1 := by
    -- sorry
    rw[coprime_mn] at this
    trivial
  norm_num at this

example {m n p : ℕ} (coprime_mn : m.coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  -- sorry
  intro sq_eq
  have pmidm:p∣m:=by
    apply Nat.Prime.dvd_of_dvd_pow
    exact prime_p
    rw[sq_eq]
    norm_num
  have existk:∃ x, m=x*p:=by
    apply dvd_iff_exists_eq_mul_left.mp pmidm
  rcases existk with ⟨k,meqpk⟩
  have: p * (p * k ^ 2)=p * n ^ 2:=by
    rw[←sq_eq,meqpk]
    ring
  have: p*k^2=n^2:=by
    rw[mul_right_inj'] at this
    trivial
    exact Nat.Prime.ne_zero prime_p
  have pmidn:p∣n:=by
    apply Nat.Prime.dvd_of_dvd_pow
    exact prime_p
    rw[←this]
    norm_num
  have: p∣Nat.gcd m n:=by
    apply Nat.dvd_gcd
    assumption
    assumption
  rw[coprime_mn] at this
  have : 2 ≤ 1 := by
    apply prime_p.two_le.trans
    exact Nat.le_of_dvd zero_lt_one this
  norm_num at this

#check Nat.factors
#check Nat.prime_of_mem_factors
#check Nat.prod_factors
#check Nat.factors_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    -- sorry
    exact factorization_pow' m 2 p

  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    -- sorry
    rw[← Nat.Prime.factorization' prime_p,← factorization_pow' n 2 p,add_comm]
    apply factorization_mul' (Nat.Prime.ne_zero prime_p) nsqr_nez p

  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} (_ : p.Prime) :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    -- sorry
    apply factorization_pow'
  have eq2 : (r.succ * n ^ k).factorization p =
      k * n.factorization p + r.succ.factorization p := by
    -- sorry
    rw[← factorization_pow' n k p,add_comm]
    apply factorization_mul'
    norm_num
    apply npow_nz
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  -- sorry
  apply Nat.dvd_sub'
  apply Nat.dvd_mul_right
  apply Nat.dvd_mul_right
#check sub_eq_add_neg
#check multiplicity
