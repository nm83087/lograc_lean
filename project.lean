import Mathlib
open BigOperators
open Finset
open Nat
open List
open Int

-- Prelims
/-
Fin n <-> [n].
Type with n elements.
Fin n is a natural number i which 0 ≤ i < n.
If i : Fin n, then:
      i.val : ℕ is this number.
      i.isLt : is the proof that i < n.
-/

/-
##### TODO ######
- Double-check if ballot sequences are well-defined in this way.
-/

-- ##### SMALL TASKS #####

-- Small task 1: Recursive definition of Catalan numbers.
def catalan_number: (n : ℕ) → ℕ
| 0 => 1
| n+1 => ∑ i : Fin (n+1), (catalan_number i * catalan_number (n-i))
-- OK

-- Small task 2: Plane trees.
inductive plane_tree : Type
| node : List plane_tree → plane_tree
--OK

-- Small task 3: Full binary trees.
inductive full_tree : Type
| leaf : full_tree
| node₂ : (T₁ T₂ : full_tree) → full_tree
--OK

-- Small task 4: Full binary trees with n non-leaf nodes.
def full_tree.nodes : full_tree → ℕ
| .leaf => 0
| .node₂ T₁ T₂ => T₁.nodes + T₂.nodes + 1
-- OK

def full_tree_n (n : ℕ) : Type
:= {T : full_tree // T.nodes = n}
-- OK

-- Small task 5: Ballot sequences (sum, length).
-- If the next term is positive, the sum and length increase.
-- If the next term is negative, the sum decreases and the length increases.
-- If the sum cannot decrease (it is ℕ, so least 0), then the sequence does not continue.
inductive ballot_sequence : ℕ → ℕ → Type
| nil : ballot_sequence 0 0
| next_pos : {sum : ℕ} → ballot_sequence sum n → ballot_sequence (succ sum) (succ n)
| next_neg : {sum : ℕ} → ballot_sequence (succ sum) n→ ballot_sequence sum (succ n)

def ballot_sequence.length : ballot_sequence bal_sum bal_len → ℕ := bal_len
-- This is all of the ballot sequences that have length n.
def ballot_sequence_n (n : ℕ) : Type :=
  ∀ (a b : ℕ),  {B : ballot_sequence a b // a = n} --probably incorrect.

-- ##### LARGE TASKS #####

-- ##### Large task 1 : Construct the bijection
-- finPiFinEquiv says: {n : ℕ} {k : Fin n → ℕ} : ((i : Fin n) → Fin (k i)) ≃ Fin (∏ i : Fin n, k i)
def finSigmaFinEquiv  {n : ℕ} {k : Fin n → ℕ} : (i : Fin n) × Fin (k i) ≃ Fin (∑ i : Fin n, k i) := by sorry

-- ##### Large task 2 : Construct the bijection between Catalan numbers.
-- If we assume showing finSigmaFinEquiv is Large Task 1, this Large Task 2 is
def catalan_product_bijection (n : ℕ) : (i : Fin (n+1)) × Fin (catalan_number i) × Fin (catalan_number (n-i)) ≃ Fin (catalan_number (n+1)) := by
  rw [catalan_number]
  apply Equiv.trans
  apply Equiv.sigmaCongrRight
  intro i
  exact finProdFinEquiv
  exact finSigmaFinEquiv

-- ##### Large task 3 : Construct a bijection between full binary trees and the type Fin Cₙ

-- ##### Large task 4 : Constuct a bijection list PlaneTree ≃ PlaneTree.
-- It is \simeq ≃ and not \iso ≅.
/-
  Constructing a bijection a ≅ b is done with Equiv.mk. It requires:
  f : a → b
  g : b → a
  left_inv : proof that g f x = x
  right_inv : proof that f g x = x
-/
def list_to_plane_tree : List plane_tree → plane_tree
| l => plane_tree.node l

def plane_tree_to_list : plane_tree → List plane_tree
| .node l => l

lemma list_to_plane_tree_to_list : ∀ (l : List plane_tree), plane_tree_to_list (list_to_plane_tree l) = l := by
  intro l
  rfl

lemma plane_tree_to_list_to_plane_tree : ∀ (T : plane_tree), list_to_plane_tree (plane_tree_to_list  T) = T := by
  intro T
  cases T
  case node => rfl

def plane_tree_bijection : List plane_tree ≃ plane_tree := Equiv.mk
  list_to_plane_tree
  plane_tree_to_list
  list_to_plane_tree_to_list
  plane_tree_to_list_to_plane_tree

-- ##### Large task 5 : Construct the rotating isomorphism between plane trees and full binary trees.

def plane_tree.cons : plane_tree → plane_tree → plane_tree
| T, plane_tree.node Ts => plane_tree.node (T :: Ts)

def full_tree.to_plane_tree : full_tree → plane_tree
| full_tree.leaf => plane_tree.node []
| full_tree.node₂ T₁ T₂ => plane_tree.cons (T₁.to_plane_tree) (T₂.to_plane_tree)

def plane_tree.to_full_tree : plane_tree → full_tree
| plane_tree.node [] => full_tree.leaf
| plane_tree.node (T :: Ts) => full_tree.node₂ T.to_full_tree (plane_tree.node Ts).to_full_tree

lemma full_to_plane_to_full : ∀ (f : full_tree), (f.to_plane_tree).to_full_tree = f := by
  intro f
  induction f with
  | leaf => rfl
  | node₂ f₁ f₂ h₁ h₂ =>
    simp [full_tree.to_plane_tree]
    unfold plane_tree.cons
    cases case_hyp : f₂.to_plane_tree --Pogruntej, kako se lepš znebit match statmeenta.
    simp
    rw [plane_tree.to_full_tree]
    simp [full_tree.to_plane_tree]
    rw [h₁, ← case_hyp, h₂]
    simp

lemma plane_to_full_to_plane : ∀ (p : plane_tree), (p.to_full_tree).to_plane_tree = p :=
  ( @plane_tree.rec
    ( fun p => p.to_full_tree.to_plane_tree = p)
    ( fun l => ( plane_tree.node l).to_full_tree.to_plane_tree = plane_tree.node l)
    ( fun n ih => ih)
    ( by rfl )
    ( fun T Ts hh th => by
      unfold plane_tree.to_full_tree
      simp
      rw [full_tree.to_plane_tree, hh, th]
      unfold plane_tree.cons
      simp
    )
  )

def rotating_isomorphism : full_tree ≃ plane_tree := Equiv.mk
  full_tree.to_plane_tree
  plane_tree.to_full_tree
  full_to_plane_to_full
  plane_to_full_to_plane

-- ##### Large task 6 : Prove that bin(2n, n) is divisible by n+1.
-- https://math.stackexchange.com/questions/189346/n1-is-a-divisor-of-binom2n-n @ Merosity

lemma binomial_fraction_property_mul (a b : ℕ) (h₀ : b ≤ a) : (a+1).choose (b+1) * (b+1) = a.choose b * (a+1) := by
  rw [
    mul_comm (a.choose b),
    a.choose_eq_factorial_div_factorial,
    ←Nat.mul_div_assoc,
    ←factorial_succ,
    choose_eq_factorial_div_factorial,
    mul_comm,
    ←Nat.mul_div_assoc,
    factorial_succ b,
    ←Nat.div_div_eq_div_mul,
    ←Nat.div_div_eq_div_mul,
    Nat.mul_div_cancel_left,
    Nat.div_div_eq_div_mul
  ]
  simp
  linarith
  apply factorial_mul_factorial_dvd_factorial
  exact Nat.succ_le_succ h₀
  exact Nat.succ_le_succ h₀
  exact factorial_mul_factorial_dvd_factorial h₀
  exact h₀

lemma euclid (a b n : ℕ) : (n ∣ a * b ∧ n.gcd a = 1) → n ∣ b := by
  intro h
  let h_n_ab := And.left h;
  let h_n_gcd_a := And.right h;
  rw [← Nat.coprime_iff_gcd_eq_one] at h_n_gcd_a
  apply h_n_gcd_a.dvd_of_dvd_mul_left
  exact h_n_ab

theorem nplus_divides_bin (n : ℕ) : (n+1) ∣ ((2*n).choose n) := by
  let x := (2*n + 1).choose (n+1);
  have hₓ : x * (n + 1) = (2*n).choose n * (2*n + 1) := by
    apply binomial_fraction_property_mul
    linarith
  have hg : (n + 1).gcd (2*n + 1) = 1 := by
    rw [n.two_mul, add_assoc]
    nth_rewrite 2 [←(n+1).one_mul]
    rw [(n+1).gcd_add_mul_self, Nat.gcd_comm, gcd_rec]
    simp
    rw [←gcd_rec, n.gcd_one_right]
  -- (n+1) divides x, but is coprime to (2n + 1), so it must divide (2n n).
  have hd : (n+1) ∣ (2*n).choose n * (2*n + 1) := by
    rw [dvd_iff_exists_eq_mul_right]
    apply Exists.intro x
    linarith
  apply euclid (2*n + 1)
  apply And.intro
  case a.left =>
    rw [mul_comm]
    exact hd
  case a.right =>
    exact hg



-- ##### Large task 7 : Prove the formula for Catalan Numbers.

/-
  suffices (catalan_number n : ℚ) = (2*n).choose n / (n+1) by
    have h := nplus_divides_bin n
    exact mod_cast this
  induction n using Nat.case_strong_induction_on
  simp
  rw [catalan_number]
-/

-- ##### Large task 8 : Construct an isomorphism Fin Cₙ ≃ BallotSequence 2n






-- ##### Graveyard of old code
/-
  induction n with
  | zero => simp; apply Equiv.equivOfIsEmpty
  | succ n ih =>
    apply Equiv.trans
    apply Equiv.sigmaCongrRight
    intro i
-/
    --refine (fun i => if h : i < n then (Fin (n+1) → Type) else Fin ())
    --apply Equiv.sigmaCongrRight




/-
-- ##### BINARY TREE #####
-- Inductive type in Lean.
-- A binary tree is a node, a node with one child, or a node with two children.
inductive bin_tree : Type
| leaf : bin_tree
| node₁ : bin_tree → bin_tree
| node₂ : bin_tree → bin_tree → bin_tree

-- A binary tree has height:
def bin_tree.height : bin_tree → ℕ
| .leaf => 1
| .node₁ T => T.height + 1
| .node₂ T₁ T₂ => max T₁.height T₂.height + 1

-- A binary tree has number of nodes:
def bin_tree.nodes : bin_tree → ℕ
| .leaf => 1
| .node₁ T => T.nodes + 1
| .node₂ T₁ T₂ => T₁.nodes + T₂.nodes + 1

-- Cast a full binary tree to an ordinary binary tree:
def full_to_bin : full_tree → bin_tree
| .leaf => .leaf
| .node₂ T₁ T₂ => .node₂ (full_to_bin T₁) (full_to_bin T₂)
-/



/-

def P (n : ℕ) : Prop := ∀ (a b : ℕ), (n ∣ a * b ∧ n.gcd a = 1) → n ∣ b

def G (n : ℕ) : Prop := n ≥ 0

def Q (c : ℕ) : Prop := ∀ (g : ℕ), ∃ (a b : ℕ), (c = a * b) → (g ∣ a * b ∧ g.gcd a = 1) → g ∣ b

def R (a b c: ℕ) : Prop := ∀ (n : ℕ), (c = a * b) → (n ∣ a * b ∧ n.gcd a = 1) → n ∣ b

lemma euclid_rec_r (a b c : ℕ) : R a b c := by
  apply Nat.strongRecOn
  (
    unfold R
    intros ic ih
    intro n h_prod h
    let h_n_div_prod_ab := And.left h;
    let h_gcd_n_a_1 := And.right h;
    rw [dvd_iff_exists_eq_mul_right] at h_n_div_prod_ab
    obtain ⟨q, h_prod_q⟩ := h_n_div_prod_ab
    by_cases h_n_eq_a : n = a
    case pos := by
      -- n = a
      rw [h_n_eq_a, Nat.gcd_self] at h_gcd_n_a_1
      have h_n_eq_1 : n = 1 := by
        apply Eq.trans h_n_eq_a h_gcd_n_a_1
      rw [h_n_eq_1]
      apply Nat.one_dvd
    case neg := by
      by_cases h_n_lt_a : n < a
      case pos := by
        -- n < a
        have h_n_le_a : n ≤ a := by
          rw [n.lt_iff_le_not_le] at h_n_lt_a
          exact And.left h_n_lt_a
        have h_arith : n * (q - b) = (a - n) * b := by
          rw [n.mul_sub_left_distrib, a.mul_sub_right_distrib]
          omega
        let d := n.gcd (a - n);
        have h_d : d = 1 := by
          have h_d_dvd_n : d ∣ n := by exact Nat.gcd_dvd_left n (a - n)
          have h_d_dvd_an : d ∣ (a-n) := by exact Nat.gcd_dvd_right n (a - n)
          have h_d_dvd_a : d ∣ a := by
            have h_d_dvd_sum : d ∣  a - n + n := by apply Nat.dvd_add h_d_dvd_an h_d_dvd_n
            rw [Nat.sub_add_cancel] at h_d_dvd_sum
            exact h_d_dvd_sum
            exact h_n_le_a
          have h_d_gcd : d ∣ n.gcd a := by
            apply Nat.dvd_gcd
            exact h_d_dvd_n
            exact h_d_dvd_a
          rw [h_gcd_n_a_1] at h_d_gcd
          apply Nat.eq_one_of_dvd_one
          exact h_d_gcd
        apply ih (a - n)
      case neg := by
        sorry
  )



lemma euclid (a b n : ℕ) : (n ∣ a * b ∧ n.gcd a = 1) → n ∣ b := by
  intro h
  let hnab := And.left h;
  let hcoprime := And.right h;
  --let hCoprime := hcoprime;
  --rw  [←n.coprime_iff_gcd_eq_one] at hCoprime
  rw [dvd_iff_exists_eq_mul_right] at hnab
  obtain ⟨q, hq⟩ := hnab
  by_cases hn_eq_a : n = a
  case pos := by
    -- n = a
    rw [hn_eq_a, Nat.gcd_self] at hcoprime
    have heq : n = 1 := by
      apply Eq.trans hn_eq_a hcoprime
    rw [heq]
    apply Nat.one_dvd
  case neg := by
    by_cases hn_lt_a : n < a
    case pos := by
    -- n < a
      have h_lthan : n ≤ a := by
        rw [n.lt_iff_le_not_le] at hn_lt_a
        exact And.left hn_lt_a
      have harith : n * (q - b) = (a - n) * b := by
        rw [n.mul_sub_left_distrib, a.mul_sub_right_distrib]
        omega
      let d := n.gcd (a - n);
      have hd : d = 1 := by
        have hgcdl : d ∣ n := by exact Nat.gcd_dvd_left n (a - n)
        have hgcdr : d ∣ (a-n) := by exact Nat.gcd_dvd_right n (a - n)
        have hgcda : d ∣ a := by
          have hgcdxx : d ∣ a - n + n := by
            apply Nat.dvd_add hgcdr hgcdl
          rw [Nat.sub_add_cancel ] at hgcdxx
          exact hgcdxx
          exact h_lthan
        have hdgcd : d ∣ n.gcd a := by
          apply Nat.dvd_gcd
          exact hgcdl
          exact hgcda
        rw [hcoprime] at hdgcd
        apply Nat.eq_one_of_dvd_one
        exact hdgcd
      sorry
        -- It is shown that d = 1.
        -- It can now be shown that 0 < (a-n) b < ab when we induct.



    -- n > a
    case neg := by
      sorry
      -- It is the exact same as above, just replace n ↔ a and b ↔ q.
-/
-- A lot of time was wasted on trying to prove Euclid's lemma inductively.
-- If I had found Nat.Coprime.dvd_of_dvd_mul_left sooner, I would have wasted a few hours less.
