import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Model

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

/- English proof (translation)
The claim follows from `(frobUr l ^ m).commutes x`.
-/
theorem fr_alg (m : ℕ) (x : ℚ_[l]) : fr l m (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) x) = algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) x :=
  (frobUr l ^ m).commutes x

/- English proof (translation)
Express the relevant statement in the definitionally equal form `algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) x) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply]`.
-/
theorem kd_alg (x : ℚ_[l]) : kd P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) x) = algebraMap ℚ_[l] P.R.BdR x := by
  change algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) x) = _
  rw [← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Polynomial.C (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) x)) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply]`.
-/
theorem ks_alg (x : ℚ_[l]) : ks P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) x) = Polynomial.C (algebraMap ℚ_[l] P.R.B x) := by
  change Polynomial.C (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) x)) = _
  rw [← IsScalarTower.algebraMap_apply]

variable {n : Type} [Fintype n] [DecidableEq n]

def diagU {R : Type} [CommRing R] (u : n → Rˣ) : GL n R where
  val := Matrix.diagonal fun j => (u j : R)
  inv := Matrix.diagonal fun j => (((u j)⁻¹ : Rˣ) : R)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

def cycSum (K : FinExt l) (a : n → ℤ) : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l) where
  toFun g := diagU fun j => Units.map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) : ℚ_[l] →* ↥(MaximalUnramifiedExtension l)) (P.χQ (g : GQ l) ^ a j)
  map_one' := by ext i j; simp [diagU]
  map_mul' g h := by
    apply Units.ext
    simp [diagU, Matrix.diagonal_mul_diagonal, mul_zpow]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cycSum_val (K : FinExt l) (a : n → ℤ) (g : ↥(GK K)) : (cycSum P K a g : Matrix n n ↥(MaximalUnramifiedExtension l)) =
    Matrix.diagonal fun j => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) ((P.χQ (g : GQ l) ^ a j : ℚ_[l]ˣ) : ℚ_[l]) := rfl

/- English proof (translation)
Rewrite using `[matD, cycSum_val, Matrix.diagonal_map (by simp)]`. Simplify using `only [fr_alg, kd_alg]`.
-/
theorem matD_cycSum (K : FinExt l) (a : n → ℤ) (m : ℕ) (g : ↥(GK K)) : matD P (cycSum P K a) m g =
    Matrix.diagonal fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a j : ℚ_[l]ˣ) : ℚ_[l]) := by
  rw [matD, cycSum_val, Matrix.diagonal_map (by simp)]
  simp only [fr_alg, kd_alg]

/- English proof (translation)
The claim follows from `hr le := hK rat g i j := by rw [cycSum_val, Matrix.diagonal_apply] split_ifs · exact fr_alg _ _ · exact map_zero _ cont i j := by simp only [cycSum_val, Matrix.diagonal_apply] split_ifs · have h := (GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.1 have h2 : Continuous fun g : ↥(GK …`.
-/
theorem isRat_cycSum {K : FinExt l} {r : ℕ} (hr : 0 < r) (hK : ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ K.1)
    (a : n → ℤ) : IsRat r (cycSum P K a) where
  pos := hr
  le := hK
  rat g i j := by
    rw [cycSum_val, Matrix.diagonal_apply]
    split_ifs
    · exact fr_alg _ _
    · exact map_zero _
  cont i j := by
    simp only [cycSum_val, Matrix.diagonal_apply]
    split_ifs
    · have h := (GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.1
      have h2 : Continuous fun g : ↥(GK K) => (P.χQ (g : GQ l) : ℚ_[l]) ^ a i :=
        (h.comp continuous_subtype_val).zpow₀ _ fun g => Or.inl (Units.ne_zero _)
      have h3 := (continuous_algebraMap ℚ_[l] (Om l)).comp h2
      refine h3.congr fun g => ?_
      simp only [Function.comp, Units.val_zpow_eq_zpow_val]
      rfl
    · exact continuous_const

/- English proof (translation)
The claim follows from `isRat_cycSum P one_pos (fun c hc => by obtain ⟨x, rfl⟩ := (GlobalTheory.MemLoc.frob_laws l (frobUr l) frobUr_root).2.2 c (by simpa [fr] using hc) exact K.1.algebraMap_mem x) a`.
-/
theorem isRat_one (K : FinExt l) (a : n → ℤ) : IsRat 1 (cycSum P K a) :=
  isRat_cycSum P one_pos (fun c hc => by
    obtain ⟨x, rfl⟩ := (GlobalTheory.MemLoc.frob_laws l (frobUr l) frobUr_root).2.2 c (by simpa [fr] using hc)
    exact K.1.algebraMap_mem x) a

/- English proof (translation)
Establish `h1 : ∀ i j : n, (1 : Matrix n n P.R.BdR) i j ∈ Fil P 0` using `fun i j => by`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `(P.PD (botExt l)).one_mem`. Conclude with `zero_mem ((P.PD (botExt l)).Fil 0)`.

Introduce `m`. Use `⟨1, ⟨h1, by simpa using h1⟩, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[matD_cycSum]`. Simplify using the standard rewrite rules.
-/
theorem framed_cycSum (K : FinExt l) (a : n → ℤ) (r : ℕ) : Framed P (cycSum P K a) (fun _ : Fin r => a) := by
  have h1 : ∀ i j : n, (1 : Matrix n n P.R.BdR) i j ∈ Fil P 0 := fun i j => by
    rw [Matrix.one_apply]
    split_ifs
    · exact (P.PD (botExt l)).one_mem
    · exact zero_mem ((P.PD (botExt l)).Fil 0)
  intro m
  refine ⟨1, ⟨h1, by simpa using h1⟩, fun g => ?_⟩
  rw [matD_cycSum]
  simp

def tU : P.R.Bˣ := (isUnit_tB P).unit

/- English proof (translation)
Establish `h : Units.map (P.actQ g : P.R.B →* P.R.B) (tU P) = Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * tU P`. Apply `Units.ext` to reduce the goal to its premises. Simplify `localPrime_galoisAction_periodT P g` using `[tU, Algebra.smul_def]`. Establish `h2` using `congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h`. Simplify using `only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h2`.

Rewrite using `[← map_zpow P.χQ]`. Conclude with `h2`.
-/
theorem actQ_tU (g : GQ l) (a : ℤ) : P.actQ g ((tU P ^ a : P.R.Bˣ) : P.R.B) =
    algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * ((tU P ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (tU P) =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * tU P := by
    apply Units.ext
    simpa [tU, Algebra.smul_def] using localPrime_galoisAction_periodT P g
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h2
  rw [← map_zpow P.χQ]
  exact h2

/- English proof (translation)
Establish `h` using `(P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b`. Rewrite `h` using `[P.PD_actB, P.PD_actdR, P.PD_ι, P.PD_ι]`. Conclude with `h.symm`.
-/
theorem actdR_ι (g : GQ l) (b : P.R.B) : P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := by
  have h := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
  rw [P.PD_actB, P.PD_actdR, P.PD_ι, P.PD_ι] at h
  exact h.symm

/- English proof (translation)
Express the relevant statement in the definitionally equal form `P.actQdR g (P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)) = _ * P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)`. Rewrite using `[actdR_ι, actQ_tU, map_mul, AlgHom.commutes]`.
-/
theorem act_tz (g : GQ l) (a : ℤ) : P.actQdR g (tz P a) =
    algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  change P.actQdR g (P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)) = _ * P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)
  rw [actdR_ι, actQ_tU, map_mul, AlgHom.commutes]

/- English proof (translation)
Introduce `m`. Take `⟨U, -, hU⟩` from `h ⟨m % r, Nat.mod_lt _ hρ.pos⟩`. Establish `hper : ∀ g, matD P ρ m g = matD P ρ (m % r) g` using `fun g => by`. Use extensionality with `i j`. Simplify using `only [matD, Matrix.map_apply]`.

Use `congr 1`. Establish `h1 : ∀ k : ℕ, (frobUr l ^ (r * k)) ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih => rw [Nat.mul_succ, pow_add, AlgHom.mul_apply]`. Use `erw [hρ.rat g i j]`. Conclude with `ih`. Express the relevant statement in the definitionally equal form `(frobUr l ^ m) _ = (frobUr l ^ (m % r)) _`. Use `conv_lhs => rw [← Nat.mod_add_div m r, pow_add, AlgHom.mul_apply, h1]`.

Use `set v := w ⟨m % r, Nat.mod_lt _ hρ.pos⟩`. Use `⟨U * diagU fun j => Units.map (P.ιB : P.R.B →* P.R.BdR) (tU P ^ (-v j)), fun g => ?_⟩` and prove the remaining obligations. Establish `e : (diagU fun j => Units.map (P.ιB : P.R.B →* P.R.BdR) (tU P ^ (-v j)) : GL n P.R.BdR).val = Matrix.diagonal fun j => tz P (-v j)` using `rfl`. Rewrite using `[Units.val_mul, e, hper, Matrix.map_mul, ← Matrix.mul_assoc, hU g, Matrix.diagonal_map (by simp), Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]`. Use `congr 2`.

Use function extensionality and compare the values at `j`. Rewrite using `[act_tz, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel]`. Simplify using the standard rewrite rules.
-/
theorem deRham_of_framed {K : FinExt l} {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (hρ : IsRat r ρ)
    {w : Fin r → n → ℤ} (h : Framed P ρ w) : AdmDR P ρ := by
  intro m
  obtain ⟨U, -, hU⟩ := h ⟨m % r, Nat.mod_lt _ hρ.pos⟩
  have hper : ∀ g, matD P ρ m g = matD P ρ (m % r) g := fun g => by
    ext i j
    simp only [matD, Matrix.map_apply]
    congr 1
    have h1 : ∀ k : ℕ, (frobUr l ^ (r * k)) ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.mul_succ, pow_add, AlgHom.mul_apply]; erw [hρ.rat g i j]; exact ih
    change (frobUr l ^ m) _ = (frobUr l ^ (m % r)) _
    conv_lhs => rw [← Nat.mod_add_div m r, pow_add, AlgHom.mul_apply, h1]
  set v := w ⟨m % r, Nat.mod_lt _ hρ.pos⟩
  refine ⟨U * diagU fun j => Units.map (P.ιB : P.R.B →* P.R.BdR) (tU P ^ (-v j)), fun g => ?_⟩
  have e : (diagU fun j => Units.map (P.ιB : P.R.B →* P.R.BdR) (tU P ^ (-v j)) : GL n P.R.BdR).val =
    Matrix.diagonal fun j => tz P (-v j) := rfl
  rw [Units.val_mul, e, hper, Matrix.map_mul, ← Matrix.mul_assoc, hU g, Matrix.diagonal_map (by simp),
    Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  congr 2
  funext j
  rw [act_tz, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel]
  simp

/- English proof (translation)
The claim follows from `deRham_of_framed P (isRat_one P K a) (framed_cycSum P K a 1)`.
-/
theorem deRham_cyclotomicSum (K : FinExt l) (a : n → ℤ) : AdmDR P (cycSum P K a) :=
  deRham_of_framed P (isRat_one P K a) (framed_cycSum P K a 1)

/- English proof (translation)
Use `⟨K, le_rfl, diagU fun j => Units.map (Polynomial.C : P.R.B →+* Bst P).toMonoidHom (tU P ^ (-a j)), fun g => ?_⟩` and prove the remaining obligations. Establish `e : (diagU fun j => Units.map (Polynomial.C : P.R.B →+* Bst P).toMonoidHom (tU P ^ (-a j)) : GL n (Bst P)).val = Matrix.diagonal fun j => Polynomial.C ((tU P ^ (-a j) : P.R.Bˣ) : P.R.B)` using `rfl`. Rewrite using `[e, cycSum_val, Matrix.diagonal_map (by simp), Matrix.diagonal_map (by simp), Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Rewrite using `[ks_alg, actSt_C, actQ_tU, ← map_mul, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel]`. Simplify using the standard rewrite rules.
-/
theorem potentiallySemistable_cyclotomicSum (K : FinExt l) (a : n → ℤ) : AdmSt P (cycSum P K a) := by
  refine ⟨K, le_rfl, diagU fun j => Units.map (Polynomial.C : P.R.B →+* Bst P).toMonoidHom (tU P ^ (-a j)), fun g => ?_⟩
  have e : (diagU fun j => Units.map (Polynomial.C : P.R.B →+* Bst P).toMonoidHom (tU P ^ (-a j)) : GL n (Bst P)).val =
    Matrix.diagonal fun j => Polynomial.C ((tU P ^ (-a j) : P.R.Bˣ) : P.R.B) := rfl
  rw [e, cycSum_val, Matrix.diagonal_map (by simp), Matrix.diagonal_map (by simp), Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  rw [ks_alg, actSt_C, actQ_tU, ← map_mul, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel]
  simp

/- English proof (translation)
Use `⟨{0}, 1, by simp, by decide, fun i j => ?_, fun g i j hi hj => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [Units.val_one, Matrix.one_apply]; split_ifs <;> simp`. Establish `: i ≠ j` using `by rintro rfl; exact hi hj`. Rewrite using `[inv_one, one_mul, mul_one, cycSum_val, Matrix.diagonal_apply_ne _ this]`.
-/
theorem splits_cycSum (K : FinExt l) (a : Fin 2 → ℤ) (r : ℕ) : Splits r (cycSum P K a) := by
  refine ⟨{0}, 1, by simp, by decide, fun i j => ?_, fun g i j hi hj => ?_⟩
  · rw [Units.val_one, Matrix.one_apply]; split_ifs <;> simp
  · have : i ≠ j := by rintro rfl; exact hi hj
    rw [inv_one, one_mul, mul_one, cycSum_val, Matrix.diagonal_apply_ne _ this]

/- English proof (translation)
Introduce and unpack `⟨s, p, ⟨x, hx⟩, hs, -⟩`. Conclude with `hs (Finset.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx)`.
-/
theorem not_splits_one {K : FinExt l} (r : ℕ) (ρ : ↥(GK K) →* GL (Fin 1) ↥(MaximalUnramifiedExtension l)) : ¬ Splits r ρ := by
  rintro ⟨s, p, ⟨x, hx⟩, hs, -⟩
  exact hs (Finset.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx)

/- English proof (translation)
Introduce `h4` and use `by have := (P.PD K).Fil_mul 1 1 _ _ (P.PD K).mem_filtration_one h4 rw [mul_one] at this exact (P.PD K).not_mem_filtration_two this`.
-/
theorem one_not_mem (K : FinExt l) : (1 : P.R.BdR) ∉ (P.PD K).Fil 1 := fun h4 => by
  have := (P.PD K).Fil_mul 1 1 _ _ (P.PD K).mem_filtration_one h4
  rw [mul_one] at this
  exact (P.PD K).not_mem_filtration_two this

/- English proof (translation)
Establish `h1 : P.ιB P.tB ∈ (P.PD K).Fil 1`. Use `(P.PD K).mem_filtration_one` as an intermediate fact. Rewrite `this` using `[P.PD_ι, P.period_datum_t_eq]`. Then use the resulting hypothesis. Establish `e : tz P ((d + 1 : ℕ) : ℤ) = P.ιB P.tB ^ (d + 1)`. Rewrite using `[tz, zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_pow]`.

Rewrite using `[e]`. Use `clear e`. Proceed by induction on `d with`. Consider the case `zero => simpa using h1`. Consider the case `succ d ih`.

Rewrite using `[pow_succ]`. Conclude with `(P.PD K).Fil_anti 1 ((P.PD K).Fil_mul 1 1 _ _ ih h1)`.
-/
theorem tz_mem (K : FinExt l) (d : ℕ) : tz P ((d + 1 : ℕ) : ℤ) ∈ (P.PD K).Fil 1 := by
  have h1 : P.ιB P.tB ∈ (P.PD K).Fil 1 := by
    have := (P.PD K).mem_filtration_one
    rwa [P.PD_ι, P.period_datum_t_eq] at this
  have e : tz P ((d + 1 : ℕ) : ℤ) = P.ιB P.tB ^ (d + 1) := by
    rw [tz, zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_pow]
  rw [e]
  clear e
  induction d with
  | zero => simpa using h1
  | succ d ih =>
    rw [pow_succ]
    exact (P.PD K).Fil_anti 1 ((P.PD K).Fil_mul 1 1 _ _ ih h1)

/- English proof (translation)
Take `⟨c, hc⟩` from `(P.PD K).invdR (u * tz P ((d + 1 : ℕ) : ℤ)) fun g => by`. Rewrite using `[P.PD_actdR, map_mul, act_tz, ← mul_assoc, mul_comm (P.actQdR _ _), h g]`. Establish `hu' : (u : P.R.BdR) ∈ (P.PD K).Fil 0`. Use `P.PD_Fil (botExt l) K 0` as an intermediate fact. Rewrite `hu` using `[Fil, this]`.

Conclude with `hu`. Establish `h2` using `(P.PD K).Fil_mul 0 1 _ _ hu' (tz_mem P K d)`. Establish `hun : IsUnit (u * tz P ((d + 1 : ℕ) : ℤ))` using `u.isUnit.mul ((Units.isUnit _).map P.ιB)`. Distinguish the cases in `hc0 : c = 0`. Rewrite `hun` using `[← hc, hc0, map_zero, isUnit_zero_iff]`.

Conclude with `one_not_mem P K (hun ▸ zero_mem _)`. Use `Submodule.smul_mem _ c⁻¹ h2` as an intermediate fact. Rewrite `this` using `[← hc, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc0, map_one, zero_add]`. Conclude with `one_not_mem P K this`.
-/
theorem no_neg (K : FinExt l) (u : P.R.BdRˣ) (hu : (u : P.R.BdR) ∈ Fil P 0) (d : ℕ)
    (h : ∀ g : ↥(GK K), algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ ((d + 1 : ℕ) : ℤ) : ℚ_[l]ˣ) : ℚ_[l]) *
      P.actQdR (g : GQ l) u = u) : False := by
  obtain ⟨c, hc⟩ := (P.PD K).invdR (u * tz P ((d + 1 : ℕ) : ℤ)) fun g => by
    rw [P.PD_actdR, map_mul, act_tz, ← mul_assoc, mul_comm (P.actQdR _ _), h g]
  have hu' : (u : P.R.BdR) ∈ (P.PD K).Fil 0 := by
    have := P.PD_Fil (botExt l) K 0
    rw [Fil, this] at hu
    exact hu
  have h2 := (P.PD K).Fil_mul 0 1 _ _ hu' (tz_mem P K d)
  have hun : IsUnit (u * tz P ((d + 1 : ℕ) : ℤ)) := u.isUnit.mul ((Units.isUnit _).map P.ιB)
  by_cases hc0 : c = 0
  · rw [← hc, hc0, map_zero, isUnit_zero_iff] at hun
    exact one_not_mem P K (hun ▸ zero_mem _)
  · have := Submodule.smul_mem _ c⁻¹ h2
    rw [← hc, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc0, map_one, zero_add] at this
    exact one_not_mem P K this

/- English proof (translation)
Use `⟨fun h => ?_, by rintro rfl; exact framed_cycSum P K _ 1⟩` and prove the remaining obligations. Take `⟨U, ⟨h1, h2⟩, hU⟩` from `h 0`. Set `u : P.R.BdRˣ` to `⟨U.val 0 0, (U⁻¹).val 0 0, by simpa [Matrix.mul_apply] using congrFun (congrFun U.mul_inv 0) 0, by simpa [Matrix.mul_apply] using congrFun (congrFun U.inv_mul 0) 0⟩`. Set `X : ↥(GK K) → ℤ → P.R.BdR` to `fun g k => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ k : ℚ_[l]ˣ) : ℚ_[l])`. Establish `hX : ∀ g j k, X g (j + k) = X g j * X g k` using `fun g j k => by simp only [X, zpow_add, Units.val_mul, map_mul]`.

Establish `hX0 : ∀ g, X g 0 = 1` using `fun g => by simp [X]`. Establish `key : ∀ g : ↥(GK K), X g a * P.actQdR (g : GQ l) u = u * X g b` using `fun g => by`. Use `congrFun (congrFun (hU g) 0) 0` as an intermediate fact. Rewrite `this` using `[matD_cycSum, Matrix.diagonal_mul, Matrix.mul_diagonal]`. Conclude with `this`.

Break down `lt_trichotomy a b with hab | hab | hab` into its components or cases. Take `⟨d, rfl⟩ : ∃ d : ℕ, b = a + ((d + 1 : ℕ) : ℤ)` from `⟨(b - a - 1).toNat, by omega⟩`. Use `(no_neg P K u⁻¹ (h2 0 0) d fun g => ?_).elim` and prove the remaining obligations. Establish `k1` using `key g`. Rewrite `k1` using `[hX]`.

Establish `k2 : P.actQdR (g : GQ l) u * P.actQdR (g : GQ l) (u⁻¹ : P.R.BdRˣ) = 1`. Rewrite using `[← map_mul, u.mul_inv, map_one]`. Establish `k3 : X g a * X g (-a) = 1` using `by rw [← hX, add_neg_cancel, hX0]`. Establish `k4` using `u.mul_inv`. Express the relevant statement in the definitionally equal form `X g _ * _ = _`.

Use `set A := P.actQdR (g : GQ l) u`. Use `set B := P.actQdR (g : GQ l) (u⁻¹ : P.R.BdRˣ)`. Use `set D := X g ((d + 1 : ℕ) : ℤ)`. Use `set w := ((u⁻¹ : P.R.BdRˣ) : P.R.BdR)`. Take the linear combination `(-(X g (-a)) * w * B) * k1 + w * k2 + (w * A * B - D * B * u * w) * k3 - D * B * k4`.

Conclude with `hab`. Take `⟨d, rfl⟩ : ∃ d : ℕ, a = b + ((d + 1 : ℕ) : ℤ)` from `⟨(a - b - 1).toNat, by omega⟩`. Use `(no_neg P K u (h1 0 0) d fun g => ?_).elim` and prove the remaining obligations. Establish `k1` using `key g`. Rewrite `k1` using `[hX]`.

Establish `k3 : X g b * X g (-b) = 1` using `by rw [← hX, add_neg_cancel, hX0]`. Express the relevant statement in the definitionally equal form `X g _ * _ = _`. Use `set A := P.actQdR (g : GQ l) u`. Use `set D := X g ((d + 1 : ℕ) : ℤ)`. Take the linear combination `(X g (-b)) * k1 + ((u : P.R.BdR) - D * A) * k3`.
-/
theorem framed_iff (K : FinExt l) (a b : ℤ) :
    Framed P (cycSum P K fun _ : Fin 1 => a) (fun (_ : Fin 1) _ => b) ↔ a = b := by
  refine ⟨fun h => ?_, by rintro rfl; exact framed_cycSum P K _ 1⟩
  obtain ⟨U, ⟨h1, h2⟩, hU⟩ := h 0
  let u : P.R.BdRˣ := ⟨U.val 0 0, (U⁻¹).val 0 0, by simpa [Matrix.mul_apply] using congrFun (congrFun U.mul_inv 0) 0,
    by simpa [Matrix.mul_apply] using congrFun (congrFun U.inv_mul 0) 0⟩
  let X : ↥(GK K) → ℤ → P.R.BdR := fun g k => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ k : ℚ_[l]ˣ) : ℚ_[l])
  have hX : ∀ g j k, X g (j + k) = X g j * X g k := fun g j k => by simp only [X, zpow_add, Units.val_mul, map_mul]
  have hX0 : ∀ g, X g 0 = 1 := fun g => by simp [X]
  have key : ∀ g : ↥(GK K), X g a * P.actQdR (g : GQ l) u = u * X g b := fun g => by
    have := congrFun (congrFun (hU g) 0) 0
    rw [matD_cycSum, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    exact this
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, b = a + ((d + 1 : ℕ) : ℤ) := ⟨(b - a - 1).toNat, by omega⟩
    refine (no_neg P K u⁻¹ (h2 0 0) d fun g => ?_).elim
    have k1 := key g
    rw [hX] at k1
    have k2 : P.actQdR (g : GQ l) u * P.actQdR (g : GQ l) (u⁻¹ : P.R.BdRˣ) = 1 := by
      rw [← map_mul, u.mul_inv, map_one]
    have k3 : X g a * X g (-a) = 1 := by rw [← hX, add_neg_cancel, hX0]
    have k4 := u.mul_inv
    change X g _ * _ = _
    set A := P.actQdR (g : GQ l) u
    set B := P.actQdR (g : GQ l) (u⁻¹ : P.R.BdRˣ)
    set D := X g ((d + 1 : ℕ) : ℤ)
    set w := ((u⁻¹ : P.R.BdRˣ) : P.R.BdR)
    linear_combination (-(X g (-a)) * w * B) * k1 + w * k2 + (w * A * B - D * B * u * w) * k3 - D * B * k4
  · exact hab
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, a = b + ((d + 1 : ℕ) : ℤ) := ⟨(a - b - 1).toNat, by omega⟩
    refine (no_neg P K u (h1 0 0) d fun g => ?_).elim
    have k1 := key g
    rw [hX] at k1
    have k3 : X g b * X g (-b) = 1 := by rw [← hX, add_neg_cancel, hX0]
    change X g _ * _ = _
    set A := P.actQdR (g : GQ l) u
    set D := X g ((d + 1 : ℕ) : ℤ)
    linear_combination (X g (-b)) * k1 + ((u : P.R.BdR) - D * A) * k3

/- English proof (translation)
Introduce `h` and use `by have h0 : (cycSum P K fun _ : Fin 1 => 0) = 1 := by ext g i j simp [cycSum_val] have := framed_cycSum P K (fun _ : Fin 1 => 0) 1 rw [h0, ← h, framed_iff] at this exact one_ne_zero this`.
-/
theorem cyc_ne_one (K : FinExt l) : (cycSum P K fun _ : Fin 1 => 1) ≠ 1 := fun h => by
  have h0 : (cycSum P K fun _ : Fin 1 => 0) = 1 := by
    ext g i j
    simp [cycSum_val]
  have := framed_cycSum P K (fun _ : Fin 1 => 0) 1
  rw [h0, ← h, framed_iff] at this
  exact one_ne_zero this

/- English proof (translation)
Set `σ : ↥(MaximalUnramifiedExtension l) ≃ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)` to `AlgEquiv.ofBijective (frobUr l) frobUr_bijective`. Establish `hσ : ∀ (k : ℕ) c, (σ ^ k) c = (frobUr l ^ k) c` using `fun k c => by`. Proceed by induction on `k generalizing c with`. Consider the case `zero => rfl`. Consider the case `succ k ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgHom.mul_apply, ih]`.

Both sides reduce to the same expression. Set `F : IntermediateField ℚ_[l] ↥(MaximalUnramifiedExtension l)` to `IntermediateField.fixedField (Subgroup.zpowers (σ ^ r))`. Establish `hF : ∀ c, c ∈ F ↔ (σ ^ r) c = c` using `fun c => by`. Rewrite using `[IntermediateField.mem_fixedField_iff]`. Use `⟨fun h => h _ (Subgroup.mem_zpowers _), fun h f hf => ?_⟩` and prove the remaining obligations.

Conclude with `(Subgroup.zpowers_le (H := MulAction.stabilizer _ c)).2 h hf`. Establish `hst : ∀ c ∈ F, σ c ∈ F` using `fun c hc => by`. Rewrite `hc`, the goal using `[hF]`. Rewrite using `[← AlgEquiv.mul_apply, ← pow_succ, pow_succ', AlgEquiv.mul_apply, hc]`. Set `τ₀ : ↥F →ₐ[ℚ_[l]] ↥F` to `((σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)).comp F.val).codRestrict F.toSubalgebra fun c => hst c c.2`.

Set `τ : ↥F ≃ₐ[ℚ_[l]] ↥F` to `AlgEquiv.ofBijective τ₀ (Algebra.IsAlgebraic.algHom_bijective _)`. Establish `hτ : ∀ (k : ℕ) (c : ↥F), (((τ ^ k) c : ↥F) : ↥(MaximalUnramifiedExtension l)) = (σ ^ k) c` using `fun k c => by`. Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← ih]`.

Both sides reduce to the same expression. Establish `hfin : IsOfFinOrder τ` using `isOfFinOrder_iff_pow_eq_one.2 ⟨r, hr, AlgEquiv.ext fun c => Subtype.ext ((hτ r c).trans ((hF c).1 c.2))⟩`. Use `haveI : Finite ↥(Subgroup.zpowers τ) := hfin.finite_zpowers`. Establish `hbot : IntermediateField.fixedField (Subgroup.zpowers τ) = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `c hc`. Rewrite `hc` using `[IntermediateField.mem_fixedField_iff]`. Take `⟨x, hx⟩` from `(GlobalTheory.MemLoc.frob_laws l (frobUr l) frobUr_root).2.2 c (congrArg Subtype.val (hc τ (Subgroup.mem_zpowers _)))`. Conclude with `⟨x, Subtype.ext hx⟩`. Use `haveI h1 : FiniteDimensional ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) ↥F := inferInstanceAs (FiniteDimensional ↥(FixedPoints.subfield (Subgroup.zpowers τ) ↥F) ↥F)`.

Use `haveI h2 : FiniteDimensional ℚ_[l] ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) := by`. Rewrite using `[hbot]`. Use `infer_instance`. Use `haveI h3 : FiniteDimensional ℚ_[l] ↥F := Module.Finite.trans ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) ↥F`. Use `⟨⟨F.map (MaximalUnramifiedExtension l).val, (F.equivMap (MaximalUnramifiedExtension l).val).toLinearEquiv.finiteDimensional⟩, fun c hc => ?_⟩` and prove the remaining obligations.

Conclude with `⟨c, (hF c).2 ((hσ r c).trans hc), rfl⟩`.
-/
theorem exists_ext {r : ℕ} (hr : 0 < r) : ∃ K : FinExt l, ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ K.1 := by
  let σ : ↥(MaximalUnramifiedExtension l) ≃ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := AlgEquiv.ofBijective (frobUr l) frobUr_bijective
  have hσ : ∀ (k : ℕ) c, (σ ^ k) c = (frobUr l ^ k) c := fun k c => by
    induction k generalizing c with
    | zero => rfl
    | succ k ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgHom.mul_apply, ih]; rfl
  let F : IntermediateField ℚ_[l] ↥(MaximalUnramifiedExtension l) := IntermediateField.fixedField (Subgroup.zpowers (σ ^ r))
  have hF : ∀ c, c ∈ F ↔ (σ ^ r) c = c := fun c => by
    rw [IntermediateField.mem_fixedField_iff]
    refine ⟨fun h => h _ (Subgroup.mem_zpowers _), fun h f hf => ?_⟩
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer _ c)).2 h hf
  have hst : ∀ c ∈ F, σ c ∈ F := fun c hc => by
    rw [hF] at hc ⊢
    rw [← AlgEquiv.mul_apply, ← pow_succ, pow_succ', AlgEquiv.mul_apply, hc]
  let τ₀ : ↥F →ₐ[ℚ_[l]] ↥F := ((σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)).comp F.val).codRestrict F.toSubalgebra
    fun c => hst c c.2
  let τ : ↥F ≃ₐ[ℚ_[l]] ↥F := AlgEquiv.ofBijective τ₀ (Algebra.IsAlgebraic.algHom_bijective _)
  have hτ : ∀ (k : ℕ) (c : ↥F), (((τ ^ k) c : ↥F) : ↥(MaximalUnramifiedExtension l)) = (σ ^ k) c := fun k c => by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← ih]; rfl
  have hfin : IsOfFinOrder τ := isOfFinOrder_iff_pow_eq_one.2 ⟨r, hr, AlgEquiv.ext fun c => Subtype.ext
    ((hτ r c).trans ((hF c).1 c.2))⟩
  haveI : Finite ↥(Subgroup.zpowers τ) := hfin.finite_zpowers
  have hbot : IntermediateField.fixedField (Subgroup.zpowers τ) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [IntermediateField.mem_fixedField_iff] at hc
    obtain ⟨x, hx⟩ := (GlobalTheory.MemLoc.frob_laws l (frobUr l) frobUr_root).2.2 c
      (congrArg Subtype.val (hc τ (Subgroup.mem_zpowers _)))
    exact ⟨x, Subtype.ext hx⟩
  haveI h1 : FiniteDimensional ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) ↥F :=
    inferInstanceAs (FiniteDimensional ↥(FixedPoints.subfield (Subgroup.zpowers τ) ↥F) ↥F)
  haveI h2 : FiniteDimensional ℚ_[l] ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) := by
    rw [hbot]; infer_instance
  haveI h3 : FiniteDimensional ℚ_[l] ↥F := Module.Finite.trans ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) ↥F
  refine ⟨⟨F.map (MaximalUnramifiedExtension l).val, (F.equivMap (MaximalUnramifiedExtension l).val).toLinearEquiv.finiteDimensional⟩, fun c hc => ?_⟩
  exact ⟨c, (hF c).2 ((hσ r c).trans hc), rfl⟩

/- English proof (translation)
Establish `h1 : algebraMap ℚ_[l] P.R.B (P.χQ g : ℚ_[l]) * P.actQ g ((tU P ^ (-1 : ℤ) : P.R.Bˣ) : P.R.B) = ((tU P ^ (-1 : ℤ) : P.R.Bˣ) : P.R.B)`. Rewrite using `[actQ_tU, ← mul_assoc, ← map_mul, ← Units.val_mul]`. Simplify using the standard rewrite rules. Establish `h2 : ((tU P ^ (-1 : ℤ) : P.R.Bˣ) : P.R.B) * P.tB = 1`. Rewrite using `[zpow_neg_one]`.

Conclude with `(tU P).inv_mul`. Use `set s := ((tU P ^ (-1 : ℤ) : P.R.Bˣ) : P.R.B)`. Establish `h1'` using `congrArg (Polynomial.C : P.R.B →+* Bst P) h1`. Establish `h2'` using `congrArg (Polynomial.C : P.R.B →+* Bst P) h2`. Rewrite `h1'`, `h2'` using `[map_mul]`.

Rewrite `h2'` using `[map_one]`. Use `ext1 i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Simplify `h1'` using `[Matrix.mul_apply, ks_alg]`. Simplify using `only [Matrix.mul_apply, ks_alg, Fin.sum_univ_two, Matrix.map_apply]`.

Simplify using `[Algebra.smul_def]`. Take the linear combination `(-(Polynomial.X + Polynomial.C (algebraMap ℚ_[l] P.R.B (kummer P g)) * Polynomial.C P.tB)) * h1' - Polynomial.C (algebraMap ℚ_[l] P.R.B (kummer P g)) * h2'`. Simplify using `[Matrix.mul_apply]`. Simplify using `[Matrix.mul_apply]`.
-/
theorem kummer_period (g : GQ l) :
    !![ks P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (P.χQ g : ℚ_[l])), ks P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (kummer P g : ℚ_[l])); 0, 1] *
      (!![Polynomial.C ((tU P ^ (-1 : ℤ) : P.R.Bˣ) : P.R.B),
        -(Polynomial.C ((tU P ^ (-1 : ℤ) : P.R.Bˣ) : P.R.B) * Polynomial.X); 0, 1] : Matrix (Fin 2) (Fin 2) (Bst P)).map
        (actSt P g) =
      !![Polynomial.C ((tU P ^ (-1 : ℤ) : P.R.Bˣ) : P.R.B),
        -(Polynomial.C ((tU P ^ (-1 : ℤ) : P.R.Bˣ) : P.R.B) * Polynomial.X); 0, 1] := by
  have h1 : algebraMap ℚ_[l] P.R.B (P.χQ g : ℚ_[l]) * P.actQ g ((tU P ^ (-1 : ℤ) : P.R.Bˣ) : P.R.B) =
      ((tU P ^ (-1 : ℤ) : P.R.Bˣ) : P.R.B) := by
    rw [actQ_tU, ← mul_assoc, ← map_mul, ← Units.val_mul]; simp
  have h2 : ((tU P ^ (-1 : ℤ) : P.R.Bˣ) : P.R.B) * P.tB = 1 := by
    rw [zpow_neg_one]; exact (tU P).inv_mul
  set s := ((tU P ^ (-1 : ℤ) : P.R.Bˣ) : P.R.B)
  have h1' := congrArg (Polynomial.C : P.R.B →+* Bst P) h1
  have h2' := congrArg (Polynomial.C : P.R.B →+* Bst P) h2
  rw [map_mul] at h1' h2'
  rw [map_one] at h2'
  ext1 i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, ks_alg] using h1'
  · simp only [Matrix.mul_apply, ks_alg, Fin.sum_univ_two, Matrix.map_apply]
    simp [Algebra.smul_def]
    linear_combination (-(Polynomial.X + Polynomial.C (algebraMap ℚ_[l] P.R.B (kummer P g)) * Polynomial.C P.tB)) * h1'
      - Polynomial.C (algebraMap ℚ_[l] P.R.B (kummer P g)) * h2'
  · simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply]

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a, by rw [pow_zero, one_mul, T.ιA]; rfl⟩`.
-/
theorem plus_ainf {AI : LocAinf l P} (T : LocTied l P AI) (a : Ainf l) : Plus T (AI.ιA a) :=
  ⟨0, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a, by rw [pow_zero, one_mul, T.ιA]; rfl⟩

/- English proof (translation)
Take `⟨P, AI, hT⟩` from `GlobalTheory.MemLoc.exists_locPrime_tied l`. Take `⟨K, hK⟩` from `exists_ext (l := l) hr`. Conclude with `⟨P, AI, hT, K, _, cyc_ne_one P K, isRat_cycSum P hr hK _, deRham_cyclotomicSum P K _, potentiallySemistable_cyclotomicSum P K _, framed_cycSum P K _ r, not_splits_one r _⟩`.
-/
theorem exists_model (l : ℕ) [Fact l.Prime] {r : ℕ} (hr : 0 < r) :
    ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) ∧
    ∃ (K : FinExt l) (ρ : ↥(GK K) →* GL (Fin 1) ↥(MaximalUnramifiedExtension l)), ρ ≠ 1 ∧ IsRat r ρ ∧ AdmDR P ρ ∧ AdmSt P ρ ∧
      Framed P ρ (fun (_ : Fin r) _ => 1) ∧ ¬ Splits r ρ := by
  obtain ⟨P, AI, hT⟩ := GlobalTheory.MemLoc.exists_locPrime_tied l
  obtain ⟨K, hK⟩ := exists_ext (l := l) hr
  exact ⟨P, AI, hT, K, _, cyc_ne_one P K, isRat_cycSum P hr hK _, deRham_cyclotomicSum P K _, potentiallySemistable_cyclotomicSum P K _,
    framed_cycSum P K _ r, not_splits_one r _⟩

end GlobalTheory.PMon.Model

end
