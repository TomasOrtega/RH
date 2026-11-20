import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns

namespace GlobalTheory.HatNF.TaylorMinus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

def Dg (L : LevelData A r) (Y : ℂ) (D : ℕ) (Z : ℂ → A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (x : ι → A), (∀ i, d i ≤ D) ∧
    (∀ s : ℂ, Z (Y - s) = ∑ i, s ^ d i • x i) ∧
    ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ∑ i, m (q + d i) * x i

variable {L : LevelData A r} {Y : ℂ}

/- English proof (translation)
Take `⟨ι, hι, d, x, hd, h1, h2⟩` from `h`. Conclude with `⟨ι, hι, d, x, fun i => (hd i).trans hDE, h1, h2⟩`.
-/
theorem Dg.mono {D E : ℕ} {Z : ℂ → A} (h : Dg L Y D Z) (hDE : D ≤ E) : Dg L Y E Z := by
  obtain ⟨ι, hι, d, x, hd, h1, h2⟩ := h
  exact ⟨ι, hι, d, x, fun i => (hd i).trans hDE, h1, h2⟩

/- English proof (translation)
Take `⟨ι, _, d, x, hd, hs, hm⟩` from `h`. Take `⟨κ, _, e, w, he, hs', hm'⟩` from `h'`. Use `⟨ι ⊕ κ, inferInstance, Sum.elim d e, Sum.elim x w, ?_, fun s => ?_, fun m hmr q => ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | j) exacts [hd i, he j]`. Simplify using `only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hs, hs']`.

Simplify using `only [add_mul, hm m hmr q, hm' m hmr q, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]`.
-/
theorem Dg.add {D : ℕ} {Z W : ℂ → A} (h : Dg L Y D Z) (h' : Dg L Y D W) :
    Dg L Y D (fun y => Z y + W y) := by
  obtain ⟨ι, _, d, x, hd, hs, hm⟩ := h
  obtain ⟨κ, _, e, w, he, hs', hm'⟩ := h'
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim d e, Sum.elim x w, ?_, fun s => ?_, fun m hmr q => ?_⟩
  · rintro (i | j)
    exacts [hd i, he j]
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hs, hs']
  · simp only [add_mul, hm m hmr q, hm' m hmr q, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/- English proof (translation)
Take `⟨ι, _, d, x, hd, hs, hm⟩` from `h`. Take `⟨κ, _, e, w, he, hs', hm'⟩` from `h'`. Use `⟨ι × κ, inferInstance, fun p => d p.1 + e p.2, fun p => x p.1 * w p.2, fun p => Nat.add_le_add (hd p.1) (he p.2), fun s => ?_, fun m hmr q => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hs, hs', Finset.sum_mul_sum, Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_smul_comm, pow_add]`. Simplify using `only`. Rewrite using `[mul_assoc, hm' m hmr q, Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_assoc, hm m hmr (q + e j), Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, show q + e j + d i = q + (d i + e j) by omega]`.
-/
theorem Dg.mul {D E : ℕ} {Z W : ℂ → A} (h : Dg L Y D Z) (h' : Dg L Y E W) :
    Dg L Y (D + E) (fun y => Z y * W y) := by
  obtain ⟨ι, _, d, x, hd, hs, hm⟩ := h
  obtain ⟨κ, _, e, w, he, hs', hm'⟩ := h'
  refine ⟨ι × κ, inferInstance, fun p => d p.1 + e p.2, fun p => x p.1 * w p.2,
    fun p => Nat.add_le_add (hd p.1) (he p.2), fun s => ?_, fun m hmr q => ?_⟩
  · dsimp only
    rw [hs, hs', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, pow_add]
  · dsimp only
    rw [mul_assoc, hm' m hmr q, Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hm m hmr (q + e j), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, show q + e j + d i = q + (d i + e j) by omega]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Unit, inferInstance, fun _ => 0, fun _ => f, fun _ => le_rfl, fun s => by simp, fun m hm q => by simp [(hf m hm q).eq]⟩`.
-/
theorem dg_const (f : A) (hf : ∀ m : ℕ → A, MulRel L m → ∀ q, Commute f (m q)) :
    Dg L Y 0 (fun _ => f) := ⟨Unit, inferInstance, fun _ => 0, fun _ => f, fun _ => le_rfl, fun s => by simp,
    fun m hm q => by simp [(hf m hm q).eq]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨Fin 2, inferInstance, ![0, 1], ![Z Y, u], by intro i; fin_cases i <;> simp, fun s => by simp [Fin.sum_univ_two, h1], fun m hm q => by simp [Fin.sum_univ_two, h2 m hm q]⟩`.
-/
theorem dg_lin (Z : ℂ → A) (u : A) (h1 : ∀ s, Z (Y - s) = Z Y + s • u)
    (h2 : ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = m q * Z Y + m (q + 1) * u) : Dg L Y 1 Z := ⟨Fin 2, inferInstance, ![0, 1], ![Z Y, u], by intro i; fin_cases i <;> simp,
    fun s => by simp [Fin.sum_univ_two, h1], fun m hm q => by simp [Fin.sum_univ_two, h2 m hm q]⟩

/- English proof (translation)
Take `⟨ι, _, d, x, hd, h1, h2⟩` from `h`. Establish `hmap : ∀ i ∈ (Finset.univ : Finset ι), d i ∈ Finset.range (D + 1)` using `fun i _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hd i))`. Use `⟨fun j => ∑ i ∈ Finset.univ.filter (fun i => d i = j), x i, fun s => ?_, fun m hm q => ?_⟩` and prove the remaining obligations. Rewrite using `[h1, ← Finset.sum_fiberwise_of_maps_to hmap]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.1 hi).2]`. Rewrite using `[h2 m hm q, ← Finset.sum_fiberwise_of_maps_to hmap]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.1 hi).2]`.
-/
theorem Dg.out {D : ℕ} {Z : ℂ → A} (h : Dg L Y D Z) :
    ∃ X : ℕ → A, (∀ s : ℂ, Z (Y - s) = ∑ j ∈ Finset.range (D + 1), s ^ j • X j) ∧
      ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ∑ j ∈ Finset.range (D + 1), m (q + j) * X j := by
  obtain ⟨ι, _, d, x, hd, h1, h2⟩ := h
  have hmap : ∀ i ∈ (Finset.univ : Finset ι), d i ∈ Finset.range (D + 1) :=
    fun i _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hd i))
  refine ⟨fun j => ∑ i ∈ Finset.univ.filter (fun i => d i = j), x i, fun s => ?_, fun m hm q => ?_⟩
  · rw [h1, ← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  · rw [h2 m hm q, ← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]

/- English proof (translation)
The claim follows from `(hm q).1 _ (by simp [LevelData.fns])`.
-/
theorem comm_c {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.c l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

/- English proof (translation)
The claim follows from `(hm q).1 _ (by simp [LevelData.fns])`.
-/
theorem comm_cb {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.cb l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

/- English proof (translation)
The claim follows from `(hm q).1 _ (by simp [LevelData.fns])`.
-/
theorem comm_cbi {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.cbi l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

/- English proof (translation)
The claim follows from `(hm q).1 _ (by simp [LevelData.fns])`.
-/
theorem comm_GG {m : ℕ → A} (hm : MulRel L m) (q : ℕ) : Commute L.GG (m q) := (hm q).1 _ (by simp [LevelData.fns])

/- English proof (translation)
The claim follows from `((hm q).1 _ (by simp [LevelData.fns])).mul_left ((hm q).1 _ (by simp [LevelData.fns]))`.
-/
theorem comm_zG {m : ℕ → A} (hm : MulRel L m) (q : ℕ) : Commute (L.ζ * L.GGi) (m q) := ((hm q).1 _ (by simp [LevelData.fns])).mul_left ((hm q).1 _ (by simp [LevelData.fns]))

/- English proof (translation)
The claim follows from `Commute.list_prod_left _ _ fun x hx => by simp only [List.mem_ofFn] at hx obtain ⟨l, rfl⟩ := hx exact h l`.
-/
theorem comm_prod {g : Fin r → A} {a : A} (h : ∀ l, Commute (g l) a) : Commute (List.ofFn g).prod a := Commute.list_prod_left _ _ fun x hx => by
    simp only [List.mem_ofFn] at hx
    obtain ⟨l, rfl⟩ := hx
    exact h l

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> fin_cases j`. Use `show Dg L Y 1 (fun y => algebraMap ℂ A y - L.pb l)`. Use `dg_lin _ (-1) (fun s => ?_) (fun m hm q => ?_)` and prove the remaining obligations. Rewrite using `[map_sub, smul_neg, Algebra.smul_def, mul_one]`. Normalize the expressions using the abelian group laws.

Rewrite using `[sub_mul, mul_sub, ((hm q).2.2.1 l), Algebra.commutes, mul_neg, mul_one]`. Normalize the expressions using the abelian group laws. Use `show Dg L Y 1 (fun _ => -L.cb l)`. Conclude with `(dg_const _ fun m hm q => (comm_cb hm q l).neg_left).mono zero_le_one`. Use `show Dg L Y 1 (fun _ => L.cbi l)`.

Conclude with `(dg_const _ fun m hm q => comm_cbi hm q l).mono zero_le_one`. Use `show Dg L Y 1 (fun _ => (0 : A))`. Conclude with `(dg_const _ fun m hm q => Commute.zero_left _).mono zero_le_one`.
-/
theorem dg_Tvl (l : Fin r) (i j : Fin 2) : Dg L Y 1 (fun y => L.Tvl y l i j) := by
  fin_cases i <;> fin_cases j
  · show Dg L Y 1 (fun y => algebraMap ℂ A y - L.pb l)
    refine dg_lin _ (-1) (fun s => ?_) (fun m hm q => ?_)
    · rw [map_sub, smul_neg, Algebra.smul_def, mul_one]
      abel
    · rw [sub_mul, mul_sub, ((hm q).2.2.1 l), Algebra.commutes, mul_neg, mul_one]
      abel
  · show Dg L Y 1 (fun _ => -L.cb l)
    exact (dg_const _ fun m hm q => (comm_cb hm q l).neg_left).mono zero_le_one
  · show Dg L Y 1 (fun _ => L.cbi l)
    exact (dg_const _ fun m hm q => comm_cbi hm q l).mono zero_le_one
  · show Dg L Y 1 (fun _ => (0 : A))
    exact (dg_const _ fun m hm q => Commute.zero_left _).mono zero_le_one

/- English proof (translation)
Proceed by induction on `ls generalizing i j with`. Consider the case `nil`. Simplify using `only [List.map_nil, List.prod_nil, List.length_nil]`. Conclude with `dg_const _ fun m hm q => by`. Rewrite using `[Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Consider the case `cons l ls ih`. Simplify using `only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two, List.length_cons]`. Conclude with `(Dg.add ((dg_Tvl l i 0).mul (ih 0 j)) ((dg_Tvl l i 1).mul (ih 1 j))).mono (by omega)`.
-/
theorem dg_list (ls : List (Fin r)) (i j : Fin 2) :
    Dg L Y ls.length (fun y => (ls.map (L.Tvl y)).prod i j) := by
  induction ls generalizing i j with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.length_nil]
    exact dg_const _ fun m hm q => by
      rw [Matrix.one_apply]
      split_ifs <;> simp
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two, List.length_cons]
    exact (Dg.add ((dg_Tvl l i 0).mul (ih 0 j)) ((dg_Tvl l i 1).mul (ih 1 j))).mono (by omega)

/- English proof (translation)
Establish `h` using `dg_list (L := L) (Y := Y) (List.ofFn (fun l : Fin r => l)).reverse i j`. Rewrite `h` using `[List.length_reverse, List.length_ofFn]`. Establish `e : (fun y => L.Tvprod y i j) = fun y => (((List.ofFn (fun l : Fin r => l)).reverse).map (L.Tvl y)).prod i j`. Use function extensionality and compare the values at `y`. Simplify using `only [LevelData.Tvprod, List.map_reverse, List.map_ofFn]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h`.
-/
theorem dg_Tvprod (i j : Fin 2) : Dg L Y r (fun y => L.Tvprod y i j) := by
  have h := dg_list (L := L) (Y := Y) (List.ofFn (fun l : Fin r => l)).reverse i j
  rw [List.length_reverse, List.length_ofFn] at h
  have e : (fun y => L.Tvprod y i j) =
      fun y => (((List.ofFn (fun l : Fin r => l)).reverse).map (L.Tvl y)).prod i j := by
    funext y
    simp only [LevelData.Tvprod, List.map_reverse, List.map_ofFn]
    rfl
  rw [e]
  exact h

/- English proof (translation)
Use `show Dg L Y 1 (fun y => -L.nabs - algebraMap ℂ A (y - 1 / 2) * (L.ζ * L.GGi))`. Use `dg_lin _ (L.ζ * L.GGi) (fun s => ?_) (fun m hm q => ?_)` and prove the remaining obligations. Rewrite using `[show Y - s - 1 / 2 = (Y - 1 / 2) - s by ring, map_sub, sub_mul, Algebra.smul_def]`. Normalize the expressions using the abelian group laws. Establish `e1` using `(hm q).2.2.2.2`.

Establish `c1` using `(comm_zG hm q).eq`. Establish `c2` using `(comm_zG hm (q + 1)).eq`. Establish `c3` using `Algebra.commutes (R := ℂ) (Y - 1 / 2) (m q)`. Establish `e0 : (-L.nabs - algebraMap ℂ A (Y - 1 / 2) * (L.ζ * L.GGi)) * m q = -(L.nabs * m q) - algebraMap ℂ A (Y - 1 / 2) * (L.ζ * L.GGi * m q)` using `by noncomm_ring`. Rewrite using `[e0, e1, c1, ← mul_assoc (algebraMap ℂ A (Y - 1 / 2)) (m q) (L.ζ * L.GGi), c3, c2]`.

Use `noncomm_ring`.
-/
theorem backwardTaylorDegree_one_mirrorLetter : Dg L Y 1 L.m0 := by
  show Dg L Y 1 (fun y => -L.nabs - algebraMap ℂ A (y - 1 / 2) * (L.ζ * L.GGi))
  refine dg_lin _ (L.ζ * L.GGi) (fun s => ?_) (fun m hm q => ?_)
  · rw [show Y - s - 1 / 2 = (Y - 1 / 2) - s by ring, map_sub, sub_mul, Algebra.smul_def]
    abel
  · have e1 := (hm q).2.2.2.2
    have c1 := (comm_zG hm q).eq
    have c2 := (comm_zG hm (q + 1)).eq
    have c3 := Algebra.commutes (R := ℂ) (Y - 1 / 2) (m q)
    have e0 : (-L.nabs - algebraMap ℂ A (Y - 1 / 2) * (L.ζ * L.GGi)) * m q =
        -(L.nabs * m q) - algebraMap ℂ A (Y - 1 / 2) * (L.ζ * L.GGi * m q) := by noncomm_ring
    rw [e0, e1, c1, ← mul_assoc (algebraMap ℂ A (Y - 1 / 2)) (m q) (L.ζ * L.GGi), c3, c2]
    noncomm_ring

/- English proof (translation)
Establish `hc : Dg L Y 0 (fun _ => L.Drb)` using `dg_const _ fun m hm q => comm_prod fun l => comm_cb hm q l`. Conclude with `(hc.mul (dg_Tvprod 0 0)).mono (by omega)`.
-/
theorem dg_Ahatv : Dg L Y (r + 1) L.Ahatv := by
  have hc : Dg L Y 0 (fun _ => L.Drb) := dg_const _ fun m hm q => comm_prod fun l => comm_cb hm q l
  exact (hc.mul (dg_Tvprod 0 0)).mono (by omega)

/- English proof (translation)
Establish `hc : Dg L Y 0 (fun _ => L.Dr * L.GG)` using `dg_const _ fun m hm q => (comm_prod fun l => comm_c hm q l).mul_left (comm_GG hm q)`. Establish `hA : Dg L Y r (fun y => L.Avr y)` using `dg_Tvprod 0 0`. Establish `hB : Dg L Y (1 + r) (fun y => L.Bvr y)` using `(dg_Tvprod 1 0).mono (by omega)`. Conclude with `(hc.mul ((backwardTaylorDegree_one_mirrorLetter.mul hA).add hB)).mono (by omega)`.
-/
theorem backwardTaylorDegree_minusHatR : Dg L Y (r + 1) L.R0v := by
  have hc : Dg L Y 0 (fun _ => L.Dr * L.GG) :=
    dg_const _ fun m hm q => (comm_prod fun l => comm_c hm q l).mul_left (comm_GG hm q)
  have hA : Dg L Y r (fun y => L.Avr y) := dg_Tvprod 0 0
  have hB : Dg L Y (1 + r) (fun y => L.Bvr y) := (dg_Tvprod 1 0).mono (by omega)
  exact (hc.mul ((backwardTaylorDegree_one_mirrorLetter.mul hA).add hB)).mono (by omega)

/- English proof (translation)
Introduce `A _ _ r L Y`. Take `⟨Xa, ha1, ha2⟩` from `(dg_Ahatv (L := L) (Y := Y)).out`. Take `⟨Xr, hr1, hr2⟩` from `(backwardTaylorDegree_minusHatR (L := L) (Y := Y)).out`. Conclude with `⟨Xa, Xr, ha1, hr1, fun m hm q => ⟨ha2 m hm q, hr2 m hm q⟩⟩`.
-/
theorem taylor_minus : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahatv (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0v (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahatv Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0v Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  intro A _ _ r L Y
  obtain ⟨Xa, ha1, ha2⟩ := (dg_Ahatv (L := L) (Y := Y)).out
  obtain ⟨Xr, hr1, hr2⟩ := (backwardTaylorDegree_minusHatR (L := L) (Y := Y)).out
  exact ⟨Xa, Xr, ha1, hr1, fun m hm q => ⟨ha2 m hm q, hr2 m hm q⟩⟩

end GlobalTheory.HatNF.TaylorMinus
