import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open Matrix PositivityTheory.GramSchwartzFunctions.EC

section Blocks

variable {R : Type} [CommRing R] {n : ℕ}

/- English proof (translation)
Unfold `blk4`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`.
-/
theorem block_matrix_mul_comm_ring (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

/- English proof (translation)
Unfold `blk4`. Rewrite using `[← Matrix.submatrix_map, Matrix.fromBlocks_map]`.
-/
theorem blk4_map_alt {S : Type} [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]

/- English proof (translation)
Unfold `blk4`. Rewrite using `[Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]`.
-/
theorem block_matrix_diagonal_one_eq_one : (blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1) = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

/- English proof (translation)
Establish `h2` using `congrArg (fun M : Matrix (Fin (n + n)) (Fin (n + n)) R => M.submatrix finSumFinEquiv finSumFinEquiv) h`. Simplify using `only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2`. Conclude with `Matrix.fromBlocks_inj.mp h2`.
-/
theorem block_matrix_injective {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M : Matrix (Fin (n + n)) (Fin (n + n)) R =>
    M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.mp h2

/- English proof (translation)
Unfold `blk4`. Rewrite using `[Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]`.
-/
theorem block_matrix_eta (g : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    g = blk4 (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
      (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂
      (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁
      (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ := by
  unfold blk4
  rw [Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]

end Blocks

/- English proof (translation)
Unfold `blk4`. Rewrite using `[Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]`.
-/
theorem block_matrix_conj_transpose {K : Type} [Field K] [StarRing K] {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    (blk4 a b c d)ᴴ = blk4 aᴴ cᴴ bᴴ dᴴ := by
  unfold blk4
  rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

end GlobalTheory.CompanionTheory.EisCellsPInv

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open Matrix PositivityTheory.GramSchwartzFunctions.EC

variable {D : D7}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jst_eq (n : ℕ) : Jst D n = blk4 0 1 (-1) 0 := rfl

/- English proof (translation)
Establish `hg` using `block_matrix_eta g`. Use `set M := g.submatrix finSumFinEquiv finSumFinEquiv`. Establish `hc : M.toBlocks₂₁ = 0`. Conclude with `Matrix.ext fun i j => hP i j`. Rewrite `hg` using `[hc]`.

Use `⟨M.toBlocks₁₁, M.toBlocks₁₂, M.toBlocks₂₂, hg, ?_⟩` and prove the remaining obligations. Rewrite `hu` using `[hg, jst_eq, block_matrix_conj_transpose, block_matrix_mul_comm_ring, block_matrix_mul_comm_ring]`. Establish `h` using `block_matrix_injective hu`. Simplify using `at h`. Conclude with `⟨h.1, h.2.1⟩`.
-/
theorem rat_form {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E)
    (hu : gᴴ * Jst D n * g = Jst D n)
    (hP : ∀ i j : Fin n, g (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0) :
    ∃ a b d : Matrix (Fin n) (Fin n) D.host.E, g = blk4 a b 0 d ∧ aᴴ * d = 1 ∧ dᴴ * a = 1 := by
  have hg := block_matrix_eta g
  set M := g.submatrix finSumFinEquiv finSumFinEquiv
  have hc : M.toBlocks₂₁ = 0 := by
    exact Matrix.ext fun i j => hP i j
  rw [hc] at hg
  refine ⟨M.toBlocks₁₁, M.toBlocks₁₂, M.toBlocks₂₂, hg, ?_⟩
  rw [hg, jst_eq, block_matrix_conj_transpose, block_matrix_mul_comm_ring, block_matrix_mul_comm_ring] at hu
  have h := block_matrix_injective hu
  simp at h
  exact ⟨h.1, h.2.1⟩

/- English proof (translation)
Simplify using `[sigR, incA, inclR]`.
-/
theorem sigR_incA (x : D.host.E) :
    sigR (AF D.host.F) D.sp.cm.sig (incA D x) = incA D (D.sp.cm.sig x) := by
  simp [sigR, incA, inclR]

/- English proof (translation)
Establish `h' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) g0.1 * Jst D n * g0.1 = Jst D n` using `h`. Use `show Formalism.UG.cT _ _ * _ * _ = _`. Establish `e1 : Units.val (Formalism.UG.bc (incA D) g0) = g0.1.map (incA D)` using `rfl`. Establish `e2 : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g0.1.map (incA D)) = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) g0.1).map (incA D)`. Use extensionality with `i j`.

Simplify using `[Formalism.UG.cT, sigR_incA]`. Rewrite using `[e1, e2, show JR (AF D.host.F) (Jst D n) = (Jst D n).map (incA D) from rfl, ← Matrix.map_mul, ← Matrix.map_mul, h']`.
-/
theorem lift_mem {n : ℕ} (g0 : GL (Fin (n + n)) D.host.E)
    (h : g0 ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n)) :
    Formalism.UG.bc (incA D) g0 ∈ HR (AF D.host.F) D.sp.cm.sig (Jst D n) := by
  have h' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) g0.1 * Jst D n * g0.1 = Jst D n := h
  show Formalism.UG.cT _ _ * _ * _ = _
  have e1 : Units.val (Formalism.UG.bc (incA D) g0) = g0.1.map (incA D) := rfl
  have e2 : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g0.1.map (incA D)) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) g0.1).map (incA D) := by
    ext i j
    simp [Formalism.UG.cT, sigR_incA]
  rw [e1, e2, show JR (AF D.host.F) (Jst D n) = (Jst D n).map (incA D) from rfl, ← Matrix.map_mul,
    ← Matrix.map_mul, h']

end GlobalTheory.CompanionTheory.EisCellsPInv

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open Matrix PositivityTheory.GramSchwartzFunctions.EC

variable {D : D7}

/- English proof (translation)
Simplify using `only [mat, map_mul, Units.val_mul]`.
-/
theorem mat_mul' {n : ℕ} (x y : G D n) : mat (x * y) = mat x * mat y := by
  simp only [mat, map_mul, Units.val_mul]

/- English proof (translation)
Take `⟨hpP, hpF⟩` from `Subgroup.mem_inf.mp hp`. Establish `hF : p.1 ∈ HFin (AF D.host.F) D.sp.cm.sig (Jst D n)` using `hpF`. Take `⟨g0, hg0, hg0p⟩` from `Subgroup.mem_map.mp hF`. Establish `hmat : mat p = g0.1.map (incA D)` using `by show p.1.1 = _`. Rewrite using `[← hg0p]`.

Both sides reduce to the same expression. Use `⟨g0, hg0, hmat, fun i j => ?_⟩` and prove the remaining obligations. Apply `incA_injective (D := D)` to reduce the goal to its premises. Rewrite using `[map_zero]`. Establish `hst` using `(Subgroup.mem_comap.mp hpP)`.

Establish `key` using `(hst (Pi.single (finSumFinEquiv (Sum.inl j)) 1)).mp ?_`. Rewrite `key` using `[upperHalf, LinearMap.mem_ker]`. Use `congrFun key i` as an intermediate fact. Simplify using `only [LinearMap.funLeft_apply, Pi.zero_apply, Matrix.mulVec_single_one] at this`. Express the relevant statement in the definitionally equal form `(mat p)ᵀ _ _ = 0 at this`.

Rewrite `this` using `[hmat]`. Conclude with `this`. Rewrite using `[upperHalf, LinearMap.mem_ker]`. Use function extensionality and compare the values at `k`. Simplify using `only [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]`.

Conclude with `Pi.single_eq_of_ne (by intro h; have := congrArg Fin.val h; simp at this; omega) _`.
-/
theorem rat_of_mem {n : ℕ} (p : G D n) (hp : p ∈ P D n ⊓ GF D n) :
    ∃ g0 : GL (Fin (n + n)) D.host.E, g0 ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) ∧
      mat p = g0.1.map (incA D) ∧
      ∀ i j : Fin n, g0.1 (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := by
  obtain ⟨hpP, hpF⟩ := Subgroup.mem_inf.mp hp
  have hF : p.1 ∈ HFin (AF D.host.F) D.sp.cm.sig (Jst D n) := hpF
  obtain ⟨g0, hg0, hg0p⟩ := Subgroup.mem_map.mp hF
  have hmat : mat p = g0.1.map (incA D) := by
    show p.1.1 = _
    rw [← hg0p]
    rfl
  refine ⟨g0, hg0, hmat, fun i j => ?_⟩
  apply incA_injective (D := D)
  rw [map_zero]
  have hst := (Subgroup.mem_comap.mp hpP)
  have key := (hst (Pi.single (finSumFinEquiv (Sum.inl j)) 1)).mp ?_
  · rw [upperHalf, LinearMap.mem_ker] at key
    have := congrFun key i
    simp only [LinearMap.funLeft_apply, Pi.zero_apply, Matrix.mulVec_single_one] at this
    change (mat p)ᵀ _ _ = 0 at this
    rw [hmat] at this
    exact this
  · rw [upperHalf, LinearMap.mem_ker]
    funext k
    simp only [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
    exact Pi.single_eq_of_ne (by intro h; have := congrArg Fin.val h; simp at this; omega) _

end GlobalTheory.CompanionTheory.EisCellsPInv

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open Matrix PositivityTheory.GramSchwartzFunctions.EC

variable {D : D7}

/- English proof (translation)
Use extensionality with `i j`. Use `show cA D (incA D (star (d i j))) = incA D (d i j)`. Rewrite using `[show cA D (incA D (star (d i j))) = incA D (star (star (d i j))) from rfl, star_star]`.
-/
theorem adj_incA {n : ℕ} (d : Matrix (Fin n) (Fin n) D.host.E) :
    adj ((dᴴ).map (incA D)) = d.map (incA D) := by
  ext i j
  show cA D (incA D (star (d i j))) = incA D (d i j)
  rw [show cA D (incA D (star (d i j))) = incA D (star (star (d i j))) from rfl, star_star]

/- English proof (translation)
Establish `h1 : a * dᴴ = 1` using `mul_eq_one_comm.mp hda`. Establish `h2 : d * aᴴ = 1` using `mul_eq_one_comm.mp had`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[block_matrix_mul_comm_ring]`. Simplify using `[h1, h2, block_matrix_diagonal_one_eq_one]`.

Rewrite using `[block_matrix_mul_comm_ring]`. Simplify using `[had, hda, block_matrix_diagonal_one_eq_one]`. Rewrite using `[jst_eq, block_matrix_conj_transpose, block_matrix_mul_comm_ring, block_matrix_mul_comm_ring]`. Simplify using `[had, hda]`.
-/
theorem ratLevi {n : ℕ} (a d : Matrix (Fin n) (Fin n) D.host.E) (had : aᴴ * d = 1) (hda : dᴴ * a = 1) :
    blk4 a 0 0 d * blk4 dᴴ 0 0 aᴴ = 1 ∧ blk4 dᴴ 0 0 aᴴ * blk4 a 0 0 d = 1 ∧
      (blk4 a 0 0 d)ᴴ * Jst D n * blk4 a 0 0 d = Jst D n := by
  have h1 : a * dᴴ = 1 := mul_eq_one_comm.mp hda
  have h2 : d * aᴴ = 1 := mul_eq_one_comm.mp had
  refine ⟨?_, ?_, ?_⟩
  · rw [block_matrix_mul_comm_ring]; simp [h1, h2, block_matrix_diagonal_one_eq_one]
  · rw [block_matrix_mul_comm_ring]; simp [had, hda, block_matrix_diagonal_one_eq_one]
  · rw [jst_eq, block_matrix_conj_transpose, block_matrix_mul_comm_ring, block_matrix_mul_comm_ring]; simp [had, hda]

/- English proof (translation)
Take `⟨g0, hg0, hmat, hlow⟩` from `rat_of_mem p hp`. Take `⟨a, b, d, hg, had, hda⟩` from `rat_form g0.1 hg0 hlow`. Take `⟨hm1, hm2, hmU⟩` from `ratLevi (D := D) (n := n) a d had hda`. Set `a0 : GL (Fin n) D.host.E` to `⟨a, dᴴ, mul_eq_one_comm.mp hda, hda⟩`. Set `m0 : GL (Fin (n + n)) D.host.E` to `⟨blk4 a 0 0 d, blk4 dᴴ 0 0 aᴴ, hm1, hm2⟩`.

Set `mEl : G D n` to `⟨Formalism.UG.bc (incA D) m0, lift_mem m0 hmU⟩`. Set `A : GL (Fin n) (AE D)` to `Formalism.UG.bc (incA D) a0`. Establish `hmEl : mat mEl = blk4 A.1 0 0 (adj (A⁻¹).1)` using `by show (blk4 a 0 0 d).map (incA D) = blk4 (a.map (incA D)) 0 0 (adj ((dᴴ).map (incA D)))`. Rewrite using `[blk4_map_alt, adj_incA, Matrix.map_zero _ (map_zero _)]`. Set `nEl : G D n` to `p * mEl⁻¹`.

Establish `hpe : p = nEl * mEl` using `by simp [nEl]`. Establish `hinv : mat mEl⁻¹ = (blk4 dᴴ 0 0 aᴴ).map (incA D)`. Simplify using `only [mat, map_inv]`. Both sides reduce to the same expression. Establish `hnEl : mat nEl = blk4 1 ((b * aᴴ).map (incA D)) 0 1`.

Rewrite using `[mat_mul', hinv, hmat, hg, ← Matrix.map_mul, block_matrix_mul_comm_ring]`. Establish `h1 : a * dᴴ = 1` using `mul_eq_one_comm.mp hda`. Establish `h2 : d * aᴴ = 1` using `mul_eq_one_comm.mp had`. Simplify using `[h1, h2, blk4_map_alt]`. Establish `hdet : Matrix.GeneralLinearGroup.det A = Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a0)`.

Use `ext`. Simplify using `[A, Formalism.UG.bc, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]`. Rewrite using `[hpe, map_mul, Module.End.mul_apply, hω.unip nEl _ hnEl, hω.levi mEl A hmEl, hdet, hχ.2]`. Establish `hab : absA D (Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a0)) = 1` using `absE_inclR _`. Simplify using `[npow, GlobalTheory.StdUnn.inner, halfTr]`.

Use `erw [hab]`. Simplify using the standard rewrite rules.
-/
theorem core {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hχ : IsHeckeChar D χ) (hω : IsWeilSch ψ χ θ V μ ω) (p : G D n) (hp : p ∈ P D n ⊓ GF D n)
    (Ψ : schwartzA θ V.rank n) : (ω p Ψ).1 0 = Ψ.1 0 := by
  obtain ⟨g0, hg0, hmat, hlow⟩ := rat_of_mem p hp
  obtain ⟨a, b, d, hg, had, hda⟩ := rat_form g0.1 hg0 hlow
  obtain ⟨hm1, hm2, hmU⟩ := ratLevi (D := D) (n := n) a d had hda
  let a0 : GL (Fin n) D.host.E := ⟨a, dᴴ, mul_eq_one_comm.mp hda, hda⟩
  let m0 : GL (Fin (n + n)) D.host.E := ⟨blk4 a 0 0 d, blk4 dᴴ 0 0 aᴴ, hm1, hm2⟩
  let mEl : G D n := ⟨Formalism.UG.bc (incA D) m0, lift_mem m0 hmU⟩
  let A : GL (Fin n) (AE D) := Formalism.UG.bc (incA D) a0
  have hmEl : mat mEl = blk4 A.1 0 0 (adj (A⁻¹).1) := by
    show (blk4 a 0 0 d).map (incA D) = blk4 (a.map (incA D)) 0 0 (adj ((dᴴ).map (incA D)))
    rw [blk4_map_alt, adj_incA, Matrix.map_zero _ (map_zero _)]
  let nEl : G D n := p * mEl⁻¹
  have hpe : p = nEl * mEl := by simp [nEl]
  have hinv : mat mEl⁻¹ = (blk4 dᴴ 0 0 aᴴ).map (incA D) := by
    simp only [mat, map_inv]
    rfl
  have hnEl : mat nEl = blk4 1 ((b * aᴴ).map (incA D)) 0 1 := by
    rw [mat_mul', hinv, hmat, hg, ← Matrix.map_mul, block_matrix_mul_comm_ring]
    have h1 : a * dᴴ = 1 := mul_eq_one_comm.mp hda
    have h2 : d * aᴴ = 1 := mul_eq_one_comm.mp had
    simp [h1, h2, blk4_map_alt]
  have hdet : Matrix.GeneralLinearGroup.det A = Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a0) := by
    ext
    simp [A, Formalism.UG.bc, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [hpe, map_mul, Module.End.mul_apply, hω.unip nEl _ hnEl, hω.levi mEl A hmEl, hdet, hχ.2]
  have hab : absA D (Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a0)) = 1 :=
    absE_inclR _
  simp [npow, GlobalTheory.StdUnn.inner, halfTr]
  erw [hab]
  simp

end GlobalTheory.CompanionTheory.EisCellsPInv

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open PositivityTheory.GramSchwartzFunctions.EC

/- English proof (translation)
Introduce `D n V ψ χ θ μ ω hS Φ γ hγ g`. Establish `hχ : IsHeckeChar D χ` using `hS.2.2.2.1`. Establish `hω : IsWeilSch ψ χ θ V μ ω` using `hS.2.2.2.2.2.2.2`. Use `show (ω (γ * g) Φ).1 0 = (ω g Φ).1 0`. Rewrite using `[map_mul, Module.End.mul_apply]`.

Conclude with `core hχ hω γ hγ _`.
-/
theorem pInv : PositivityTheory.GramSchwartzFunctions.EC.PInv := by
  intro D n V ψ χ θ μ ω hS Φ γ hγ g
  have hχ : IsHeckeChar D χ := hS.2.2.2.1
  have hω : IsWeilSch ψ χ θ V μ ω := hS.2.2.2.2.2.2.2
  show (ω (γ * g) Φ).1 0 = (ω g Φ).1 0
  rw [map_mul, Module.End.mul_apply]
  exact core hχ hω γ hγ _

end GlobalTheory.CompanionTheory.EisCellsPInv
