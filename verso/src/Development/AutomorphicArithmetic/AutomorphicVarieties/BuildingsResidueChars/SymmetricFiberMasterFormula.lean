import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberSumOverFibers
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberIndexFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberStabilizerFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberOfBot
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberCardFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberCovering

open MulAction in
/- English proof (translation)
Introduce `Γ G _ _ ι S U U' Γ₁ Γ₀ ι₁ hι₁ hcomm hΓ₁ hΓ₀ htriv hUU' hidx hfinT hfinS hT hstab`. Use `haveI hSN : S.Normal := ⟨fun s hs g => by`. Establish `h` using `S.mul_mem (hcomm g s) hs`. Simplify `h⟩` using `[mul_assoc]`. Establish `hcomp : S.subtype.comp ι₁ = ι.comp Γ₁.subtype` using `MonoidHom.ext fun γ => hι₁ γ`.

Establish `hsub : Γ₁ ≤ S.comap ι` using `fun γ hγ => by`. Establish `h` using `(ι₁ ⟨γ, hγ⟩).2`. Rewrite `h` using `[hι₁]`. Conclude with `h`. Establish `hfinU' : ∀ g : G, {h : Γ₁ | g⁻¹ * ι₁ h * g ∈ U'}.Finite` using `fun g => UpperTheory.orbitalFiber_stabilizer_finite Γ₁ G S U U' ι₁ g hSN hidx (hfinS g)`.

Establish `hn : Nat.card (Γ₀.subgroupOf Γ₁) ≠ 0`. Establish `hsubset : ((Γ₀.subgroupOf Γ₁ : Subgroup Γ₁) : Set Γ₁) ⊆ {h : Γ₁ | (1 : G)⁻¹ * ι₁ h * 1 ∈ U'}`. Introduce `z hz`. Establish `hz' : (z : Γ) ∈ Γ₀` using `Subgroup.mem_subgroupOf.1 hz`. Establish `h` using `htriv _ hz' ((1 : G) : G ⧸ U')`.

Rewrite `h` using `[MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]`. Establish `h' : ι z ∈ U'` using `by simpa using U'.inv_mem h`. Simplify `h'` using `[hι₁]`. Use `haveI : Finite (Γ₀.subgroupOf Γ₁) := ((hfinU' 1).subset hsubset).to_subtype`. Conclude with `Nat.card_pos.ne'`.

Establish `hd : (Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) ≠ 0`. Use `UpperTheory.orbitalFiber_index_finite Γ G ι S U' Γ₁ Γ₀ hSN hΓ₁ ?_ ?_` and prove the remaining obligations. Take `⟨T, hT1⟩` from `hfinT 1`. Use `⟨T.image (fun t : S => (t : G)), fun s hs => ?_⟩` and prove the remaining obligations. Take `⟨h, t, ht, u, hu, e⟩` from `hT1 ⟨s, hs⟩`.

Use `⟨h, h.2, t, Finset.mem_image_of_mem _ ht, u, hUU' (by simpa using hu), ?_⟩` and prove the remaining obligations. Establish `e'` using `congrArg (Subtype.val) e`. Simplify `e'` using `[hι₁]`. Establish `h` using `hstab ((1 : G) : G ⧸ U')`. Rewrite `h` using `[MulAction.stabilizer_quotient]`. Then use the resulting hypothesis.

Establish `hn' : (Nat.card (Γ₀.subgroupOf Γ₁) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hn`. Use `⟨(U.relIndex (U' ⊓ S) : ℝ) * ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℝ) / (Nat.card (Γ₀.subgroupOf Γ₁) : ℝ), ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (0 : ℝ) < (U.relIndex (U' ⊓ S) : ℝ)` using `Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx)`. Establish `h2 : (0 : ℝ) < ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℝ)` using `Nat.cast_pos.2 (Nat.pos_of_ne_zero hd)`. Establish `h3 : (0 : ℝ) < (Nat.card (Γ₀.subgroupOf Γ₁) : ℝ)` using `Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)`.

Conclude with `div_pos (mul_pos h1 h2) h3`. Introduce `I _ x Ux Φ hij hcov hUx hΦl hΦr`. Rewrite using `[UpperTheory.orbitalFiber_sum_over_fibers Γ G I ι S U' Γ₀ x Φ hcomm hΓ₀ hΦl hΦr hT hij hcov, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hcover` using `UpperTheory.symmetric_fiber_covering Γ₁ G S U U' (x i) (Ux i) ι₁ Φ hSN hUU' (hUx i) hidx (fun h g => by rw [hι₁]; exact hΦl _ _) hΦr (by`.

Take `⟨T, hT1⟩` from `hfinT (x i)`. Use `⟨T, fun s => ?_⟩` and prove the remaining obligations. Take `⟨h, t, ht, u, hu, e⟩` from `hT1 s`. Conclude with `⟨h, t, ht, u, (hUx i u).2 hu, e⟩)`. Use the proof step `hfinU'`.

Establish `hone` using `UpperTheory.orbitalFiber_single Γ G ι S U' Γ₁ Γ₀ (x i) Φ hcomm hsub hΓ₀ htriv hΦl hΦr (by`. Take `⟨T, hT1⟩` from `hfinT (x i)`. Use `⟨T.image (fun t : S => (t : G) * x i), fun s hs => ?_⟩` and prove the remaining obligations. Take `⟨h, t, ht, u, hu, e⟩` from `hT1 ⟨s, hs⟩`. Use `⟨h, h.2, _, Finset.mem_image_of_mem _ ht, _, hUU' hu, ?_⟩` and prove the remaining obligations.

Establish `e' : s = ι h * t * u`. Establish `e2` using `congrArg (Subtype.val) e`. Simplify `e2` using `[hι₁]`. Rewrite using `[e']`. Use the proof step `group)`.

Use `hstab hd hn`. Rewrite using `[hcover, hcomp]`. Establish `hC : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) ⊥ U' ((orbit S (x i : G ⧸ U')).indicator fun y => Φ y.out) = ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℂ) * UpperTheory.V.Z.Sym.gqOn (ι.comp ((S ⊔ U').comap ι).subtype) (Γ₀.subgroupOf ((S ⊔ U').comap ι)) U' ((orbit S (x i : G ⧸ U') …`. Rewrite using `[eq_div_iff hn', mul_comm]`. Conclude with `hone`.

Rewrite using `[hC]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.symmetric_fiber_master_formula :
    UpperTheory.V.Z.Sym.Glob.Fib.Master := by
  intro Γ G _ _ ι S U U' Γ₁ Γ₀ ι₁ hι₁ hcomm hΓ₁ hΓ₀ htriv hUU' hidx hfinT hfinS hT hstab
  classical
  haveI hSN : S.Normal := ⟨fun s hs g => by
    have h := S.mul_mem (hcomm g s) hs
    simpa [mul_assoc] using h⟩
  have hcomp : S.subtype.comp ι₁ = ι.comp Γ₁.subtype := MonoidHom.ext fun γ => hι₁ γ
  have hsub : Γ₁ ≤ S.comap ι := fun γ hγ => by
    have h := (ι₁ ⟨γ, hγ⟩).2
    rw [hι₁] at h
    exact h
  have hfinU' : ∀ g : G, {h : Γ₁ | g⁻¹ * ι₁ h * g ∈ U'}.Finite := fun g =>
    UpperTheory.orbitalFiber_stabilizer_finite Γ₁ G S U U' ι₁ g hSN hidx (hfinS g)

  have hn : Nat.card (Γ₀.subgroupOf Γ₁) ≠ 0 := by
    have hsubset : ((Γ₀.subgroupOf Γ₁ : Subgroup Γ₁) : Set Γ₁) ⊆ {h : Γ₁ | (1 : G)⁻¹ * ι₁ h * 1 ∈ U'} := by
      intro z hz
      have hz' : (z : Γ) ∈ Γ₀ := Subgroup.mem_subgroupOf.1 hz
      have h := htriv _ hz' ((1 : G) : G ⧸ U')
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq] at h
      have h' : ι z ∈ U' := by simpa using U'.inv_mem h
      simpa [hι₁] using h'
    haveI : Finite (Γ₀.subgroupOf Γ₁) := ((hfinU' 1).subset hsubset).to_subtype
    exact Nat.card_pos.ne'
  have hd : (Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) ≠ 0 := by
    refine UpperTheory.orbitalFiber_index_finite Γ G ι S U' Γ₁ Γ₀ hSN hΓ₁ ?_ ?_
    · obtain ⟨T, hT1⟩ := hfinT 1
      refine ⟨T.image (fun t : S => (t : G)), fun s hs => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 ⟨s, hs⟩
      refine ⟨h, h.2, t, Finset.mem_image_of_mem _ ht, u, hUU' (by simpa using hu), ?_⟩
      have e' := congrArg (Subtype.val) e
      simpa [hι₁] using e'
    · have h := hstab ((1 : G) : G ⧸ U')
      rwa [MulAction.stabilizer_quotient] at h
  have hn' : (Nat.card (Γ₀.subgroupOf Γ₁) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨(U.relIndex (U' ⊓ S) : ℝ) * ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℝ) /
    (Nat.card (Γ₀.subgroupOf Γ₁) : ℝ), ?_, ?_⟩
  · have h1 : (0 : ℝ) < (U.relIndex (U' ⊓ S) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx)
    have h2 : (0 : ℝ) < ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hd)
    have h3 : (0 : ℝ) < (Nat.card (Γ₀.subgroupOf Γ₁) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    exact div_pos (mul_pos h1 h2) h3
  intro I _ x Ux Φ hij hcov hUx hΦl hΦr
  rw [UpperTheory.orbitalFiber_sum_over_fibers Γ G I ι S U' Γ₀ x Φ hcomm hΓ₀ hΦl hΦr hT hij hcov, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcover := UpperTheory.symmetric_fiber_covering Γ₁ G S U U' (x i) (Ux i) ι₁ Φ hSN hUU' (hUx i) hidx
    (fun h g => by rw [hι₁]; exact hΦl _ _) hΦr
    (by
      obtain ⟨T, hT1⟩ := hfinT (x i)
      refine ⟨T, fun s => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 s
      exact ⟨h, t, ht, u, (hUx i u).2 hu, e⟩)
    hfinU'
  have hone := UpperTheory.orbitalFiber_single Γ G ι S U' Γ₁ Γ₀ (x i) Φ hcomm hsub hΓ₀ htriv hΦl hΦr
    (by
      obtain ⟨T, hT1⟩ := hfinT (x i)
      refine ⟨T.image (fun t : S => (t : G) * x i), fun s hs => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 ⟨s, hs⟩
      refine ⟨h, h.2, _, Finset.mem_image_of_mem _ ht, _, hUU' hu, ?_⟩
      have e' : s = ι h * t * u := by
        have e2 := congrArg (Subtype.val) e
        simpa [hι₁] using e2
      rw [e']
      group)
    hstab hd hn
  rw [hcover, hcomp]
  have hC : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) ⊥ U'
      ((orbit S (x i : G ⧸ U')).indicator fun y => Φ y.out) =
      ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℂ) *
        UpperTheory.V.Z.Sym.gqOn (ι.comp ((S ⊔ U').comap ι).subtype) (Γ₀.subgroupOf ((S ⊔ U').comap ι)) U'
          ((orbit S (x i : G ⧸ U')).indicator fun y => Φ y.out) / (Nat.card (Γ₀.subgroupOf Γ₁) : ℂ) := by
    rw [eq_div_iff hn', mul_comm]
    exact hone
  rw [hC]
  push_cast
  ring
