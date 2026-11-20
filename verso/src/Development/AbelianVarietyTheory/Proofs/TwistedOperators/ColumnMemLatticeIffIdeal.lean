import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.UnitaryEmbeddingColumns

open GlobalTheory.FinPl GlobalTheory.SeeSaw

/- English proof (translation)
Use `B.herm.eq (B.frame i) (B.frame j)` as an intermediate fact. Simplify `this` using `[HSpace.gram, starRingEnd_apply]`.
-/
theorem gram_star {D : D7} (B : HSp D) (i j : Fin B.rank) : star (B.gram i j) = B.gram j i := by
  have := B.herm.eq (B.frame i) (B.frame j)
  simpa [HSpace.gram, starRingEnd_apply] using this

/- English proof (translation)
Use `show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (y ⊗ₜ[D.host.F] z) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.
-/
theorem incA_mul_tmul' {D : D7} (e : D.host.E) (y : AF D.host.F) (z : D.host.E) :
    incA D e * (y ⊗ₜ[D.host.F] z) = y ⊗ₜ[D.host.F] (e * z) := by
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (y ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/- English proof (translation)
Use `show (y ⊗ₜ[D.host.F] t) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`.
-/
theorem tmul_mul_incA {D : D7} (y : AF D.host.F) (t e : D.host.E) :
    (y ⊗ₜ[D.host.F] t) * incA D e = y ⊗ₜ[D.host.F] (t * e) := by
  show (y ⊗ₜ[D.host.F] t) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `set r : Fin c := q.rev with hr`. Use `set κ : D.host.E := antiDiagonalSignGramMatrix c ε r q with hκdef`. Establish `hcond : ∀ p : Fin c, (r.1 + p.1 + 1 = c ↔ p = q)`. Introduce `p`. Use `q.2` as an intermediate fact.

Use `p.2` as an intermediate fact. Rewrite using `[hr, Fin.val_rev, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Establish `hκ : κ ≠ 0`. Rewrite using `[hκdef, antiDiagonalSignGramMatrix, if_pos ((hcond q).2 rfl)]`.

Use `split_ifs`. Conclude with `hε`. Conclude with `one_ne_zero`. Set `π : Fin B.rank → D.host.E` to `fun j => κ⁻¹ * ∑ l, star (d.a l r) * B.gram l j`. Establish `hπa : ∀ p, ∑ j, π j * d.a j p = if p = q then 1 else 0`.

Introduce `p`. Establish `e` using `congrFun (congrFun d.gram r) p`. Simplify using `only [Matrix.mul_apply, Formalism.UG.cT, transpose_apply, map_apply] at e`. Establish `e2 : ∑ j, π j * d.a j p = κ⁻¹ * antiDiagonalSignGramMatrix c ε r p`. Rewrite using `[← e, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [π]`. Rewrite using `[mul_assoc]`. Use `congr 2`. Rewrite using `[e2]`.

Use `split_ifs with hp`. Substitute `hp` using the available equality. Rewrite using `[← hκdef]`. Conclude with `inv_mul_cancel₀ hκ`. Rewrite using `[antiDiagonalSignGramMatrix, if_neg (fun h' => hp ((hcond p).1 h')), mul_zero]`.

Establish `hπM : ∀ i, ∑ j, π j * frameMat B A d.ι j i = 0`. Introduce `i`. Establish `e` using `congrFun (congrFun d.perp i) r`. Simplify using `only [Matrix.mul_apply, Formalism.UG.cT, transpose_apply, map_apply, Matrix.zero_apply] at e`. Establish `hsig : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x` using `fun _ => rfl`.

Establish `e3 : ∑ j, π j * frameMat B A d.ι j i = κ⁻¹ * ∑ j, ∑ l, star (d.a l r) * B.gram l j * frameMat B A d.ι j i`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [π]`. Rewrite using `[mul_assoc, Finset.sum_mul]`.

Rewrite using `[e3]`. Establish `e4 : ∑ j, ∑ l, star (d.a l r) * B.gram l j * frameMat B A d.ι j i = star (∑ l, (∑ x, (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι x i) * B.gram x l) * d.a l r)`. Simplify using `only [star_sum, star_mul', Finset.sum_mul, hsig, star_star, gram_star]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e4, e, star_zero, mul_zero]`. Set `Φ : (Fin B.rank → AE D) →+ AE D` to `{ toFun := fun Y => ∑ k, incA D (π k) * Y k map_zero' := by simp map_add' := fun Y Z => by simp [mul_add, Finset.sum_add_distrib] }`. Establish `hΦ : ∀ Y ∈ latV B (d.lat Λ 𝔟) (· = v), Φ Y ∈ idV (𝔟 q) v`. Introduce `Y hY`.

Proceed by induction on `hY using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, hαv, a, ha, x, hx, rfl⟩` from `hy`. Rewrite `ha` using `[Set.mem_singleton_iff]`. Substitute `ha` using the available equality.

Take `⟨y, -, u, hu, rfl⟩` from `hx`. Establish `e : Φ (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) i)) = pairA D.host.F 0 α ⊗ₜ[D.host.F] u q` using `by show ∑ k, incA D (π k) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) k)) = _`. Simplify using `only [incA_mul_tmul', one_mul]`. Rewrite using `[← TensorProduct.tmul_sum]`. Use `congr 1`.

Establish `h1 : ∑ k, π k * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) k = ∑ i, (∑ j, π j * frameMat B A d.ι j i) * y i + ∑ p, (∑ j, π j * d.a j p) * u p`. Simplify using `only [Pi.add_apply, mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]`. Use `congr 1`. Rewrite using `[Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.

Rewrite using `[h1]`. Simplify using `only [hπM, hπa, zero_mul, Finset.sum_const_zero, zero_add, ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[e]`. Conclude with `AddSubgroup.subset_closure ⟨α, hα, hαv, u q, hu q, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add Y Z _ _ hY hZ => rw [map_add]`. Conclude with `add_mem hY hZ`. Consider the case `neg Y _ hY => rw [map_neg]`. Conclude with `neg_mem hY`.

Establish `key` using `hΦ _ h`. Establish `e : Φ (fun k => b * incA D (d.a k q)) = b` using `by show ∑ k, incA D (π k) * (b * incA D (d.a k q)) = b`. Establish `: ∀ k, incA D (π k) * (b * incA D (d.a k q)) = b * incA D (π k * d.a k q)` using `fun k => by`. Rewrite using `[map_mul (incA D) (π k) (d.a k q)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, ← map_sum, hπa q, if_pos rfl, map_one, mul_one]`. Rewrite `key` using `[e]`. Then use the resulting hypothesis.
-/
theorem mem_idV_of_mem {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    (q : Fin c) (b : AE D)
    (h : (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v)) : b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v := by
  classical
  set r : Fin c := q.rev with hr
  set κ : D.host.E := antiDiagonalSignGramMatrix c ε r q with hκdef
  have hcond : ∀ p : Fin c, (r.1 + p.1 + 1 = c ↔ p = q) := by
    intro p
    have := q.2; have := p.2
    rw [hr, Fin.val_rev, Fin.ext_iff]; omega
  have hκ : κ ≠ 0 := by
    rw [hκdef, antiDiagonalSignGramMatrix, if_pos ((hcond q).2 rfl)]
    split_ifs
    · exact hε
    · exact one_ne_zero
  let π : Fin B.rank → D.host.E := fun j => κ⁻¹ * ∑ l, star (d.a l r) * B.gram l j
  have hπa : ∀ p, ∑ j, π j * d.a j p = if p = q then 1 else 0 := by
    intro p
    have e := congrFun (congrFun d.gram r) p
    simp only [Matrix.mul_apply, Formalism.UG.cT, transpose_apply, map_apply] at e
    have e2 : ∑ j, π j * d.a j p = κ⁻¹ * antiDiagonalSignGramMatrix c ε r p := by
      rw [← e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [π]
      rw [mul_assoc]
      congr 2
    rw [e2]
    split_ifs with hp
    · subst hp; rw [← hκdef]; exact inv_mul_cancel₀ hκ
    · rw [antiDiagonalSignGramMatrix, if_neg (fun h' => hp ((hcond p).1 h')), mul_zero]
  have hπM : ∀ i, ∑ j, π j * frameMat B A d.ι j i = 0 := by
    intro i
    have e := congrFun (congrFun d.perp i) r
    simp only [Matrix.mul_apply, Formalism.UG.cT, transpose_apply, map_apply, Matrix.zero_apply] at e
    have hsig : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := fun _ => rfl
    have e3 : ∑ j, π j * frameMat B A d.ι j i =
        κ⁻¹ * ∑ j, ∑ l, star (d.a l r) * B.gram l j * frameMat B A d.ι j i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [π]
      rw [mul_assoc, Finset.sum_mul]
    rw [e3]
    have e4 : ∑ j, ∑ l, star (d.a l r) * B.gram l j * frameMat B A d.ι j i =
        star (∑ l, (∑ x, (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι x i) * B.gram x l) * d.a l r) := by
      simp only [star_sum, star_mul', Finset.sum_mul, hsig, star_star, gram_star]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e4, e, star_zero, mul_zero]
  let Φ : (Fin B.rank → AE D) →+ AE D :=
    { toFun := fun Y => ∑ k, incA D (π k) * Y k
      map_zero' := by simp
      map_add' := fun Y Z => by simp [mul_add, Finset.sum_add_distrib] }
  have hΦ : ∀ Y ∈ latV B (d.lat Λ 𝔟) (· = v), Φ Y ∈ idV (𝔟 q) v := by
    intro Y hY
    induction hY using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, hαv, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨y, -, u, hu, rfl⟩ := hx
      have e : Φ (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) i)) =
          pairA D.host.F 0 α ⊗ₜ[D.host.F] u q := by
        show ∑ k, incA D (π k) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) k)) = _
        simp only [incA_mul_tmul', one_mul]
        rw [← TensorProduct.tmul_sum]
        congr 1
        have h1 : ∑ k, π k * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) k =
            ∑ i, (∑ j, π j * frameMat B A d.ι j i) * y i + ∑ p, (∑ j, π j * d.a j p) * u p := by
          simp only [Pi.add_apply, mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.sum_mul]
          congr 1
          · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        rw [h1]
        simp only [hπM, hπa, zero_mul, Finset.sum_const_zero, zero_add, ite_mul, one_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [e]
      exact AddSubgroup.subset_closure ⟨α, hα, hαv, u q, hu q, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add Y Z _ _ hY hZ => rw [map_add]; exact add_mem hY hZ
    | neg Y _ hY => rw [map_neg]; exact neg_mem hY
  have key := hΦ _ h
  have e : Φ (fun k => b * incA D (d.a k q)) = b := by
    show ∑ k, incA D (π k) * (b * incA D (d.a k q)) = b
    have : ∀ k, incA D (π k) * (b * incA D (d.a k q)) = b * incA D (π k * d.a k q) := fun k => by
      rw [map_mul (incA D) (π k) (d.a k q)]; ring
    rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, ← map_sum, hπa q, if_pos rfl, map_one, mul_one]
  rwa [e] at key

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Set `Ψ : AE D →+ (Fin B.rank → AE D)` to `AddMonoidHom.pi fun k => AddMonoidHom.mulRight (incA D (d.a k q))`. Establish `hle : idV (𝔟 q) v ≤ (latV B (d.lat Λ 𝔟) (· = v)).comap Ψ`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨α, hα, hαv, t, ht, rfl⟩`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises.

Use `⟨α, hα, hαv, 1, Set.mem_singleton _, d.a *ᵥ Pi.single q t, ?_, ?_⟩` and prove the remaining obligations. Use `⟨0, Λ.zero_mem, Pi.single q t, fun p => ?_, by simp⟩` and prove the remaining obligations. Distinguish the cases in `hp : p = q`. Substitute `hp` using the available equality. Simplify using `using ht`.

Rewrite using `[Pi.single_eq_of_ne hp]`. Conclude with `(𝔟 p).zero_mem`. Use function extensionality and compare the values at `k show (pairA D.host.F 0 α ⊗ₜ[D.host.F] t) * incA D (d.a k q) = _`. Rewrite using `[tmul_mul_incA, one_mul]`. Use `congr 1`.

Rewrite using `[mulVec_single, Pi.smul_apply, op_smul_eq_mul, Matrix.col_apply, mul_comm]`. Conclude with `hle h`.
-/
theorem mem_of_mem_idV {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    (q : Fin c) (b : AE D)
    (h : b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v) : (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v) := by
  classical
  let Ψ : AE D →+ (Fin B.rank → AE D) := AddMonoidHom.pi fun k => AddMonoidHom.mulRight (incA D (d.a k q))
  have hle : idV (𝔟 q) v ≤ (latV B (d.lat Λ 𝔟) (· = v)).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, t, ht, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, hαv, 1, Set.mem_singleton _, d.a *ᵥ Pi.single q t, ?_, ?_⟩
    · refine ⟨0, Λ.zero_mem, Pi.single q t, fun p => ?_, by simp⟩
      by_cases hp : p = q
      · subst hp; simpa using ht
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · funext k
      show (pairA D.host.F 0 α ⊗ₜ[D.host.F] t) * incA D (d.a k q) = _
      rw [tmul_mul_incA, one_mul]
      congr 1
      rw [mulVec_single, Pi.smul_apply, op_smul_eq_mul, Matrix.col_apply, mul_comm]
  exact hle h

/- English proof (translation)
Assemble the required witnesses or components as `⟨mem_idV_of_mem d hε Λ 𝔟 v q b, mem_of_mem_idV d Λ 𝔟 v q b⟩`.
-/
theorem mem_latV_iff {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    (q : Fin c) (b : AE D) :
    (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v) ↔ b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v :=
  ⟨mem_idV_of_mem d hε Λ 𝔟 v q b, mem_of_mem_idV d Λ 𝔟 v q b⟩

end GlobalTheory.UnitaryEmbeddingColumns

end
