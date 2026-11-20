import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FinD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.CentFin

open MulAction UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Tf

section

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] {B : Base Γ G V} {s : B.Tw} {f : G → ℂ}

private noncomputable def FF (s : B.Tw) (f : G → ℂ) (δ : Γ) (y : G ⧸ B.U) : ℂ := s.ker f δ y * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ)

/- English proof (translation)
Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul B.U g`. Unfold `Base.Tw.ker`. Rewrite using `[hu]`. Establish `e : (g * (u : G))⁻¹ * B.ι δ * s.θ (g * u) = ((u⁻¹ : B.U) : G) * (g⁻¹ * B.ι δ * s.θ g * s.θ u)`. Simplify using `only [map_mul, mul_inv_rev, Subgroup.coe_inv, mul_assoc]`.

Rewrite using `[e, hf.left, hf.right, map_inv]`. Simplify using the standard rewrite rules.
-/
private theorem ker_mk (hf : s.IsTest f) (δ : Γ) (g : G) : s.ker f δ g = f (g⁻¹ * B.ι δ * s.θ g) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U g
  unfold Base.Tw.ker
  rw [hu]
  have e : (g * (u : G))⁻¹ * B.ι δ * s.θ (g * u) = ((u⁻¹ : B.U) : G) * (g⁻¹ * B.ι δ * s.θ g * s.θ u) := by
    simp only [map_mul, mul_inv_rev, Subgroup.coe_inv, mul_assoc]
  rw [e, hf.left, hf.right, map_inv]
  simp

/- English proof (translation)
Unfold `FF Tk Base.Tw.ker`. Establish `hθ : s.θ (B.ι (s.θΓ.symm δ) * Quotient.out y) = B.ι δ * s.θ (Quotient.out y)`. Rewrite using `[map_mul, s.comm, MulEquiv.apply_symm_apply]`. Establish `hL : s.Θ ∘ₗ B.W (s.θΓ.symm δ) = B.W δ ∘ₗ s.Θ`. Use extensionality with `v`.

Simplify using `[s.int]`. Rewrite using `[hθ, hL, map_smul, smul_eq_mul]`. Simplify using `only [mul_assoc]`.
-/
private theorem FF_tr (δ : Γ) (y : G ⧸ B.U) : FF s f δ y = LinearMap.trace ℂ V (Tk s f y.out y.out (s.θΓ.symm δ)) := by
  unfold FF Tk Base.Tw.ker
  have hθ : s.θ (B.ι (s.θΓ.symm δ) * Quotient.out y) = B.ι δ * s.θ (Quotient.out y) := by
    rw [map_mul, s.comm, MulEquiv.apply_symm_apply]
  have hL : s.Θ ∘ₗ B.W (s.θΓ.symm δ) = B.W δ ∘ₗ s.Θ := by
    ext v
    simp [s.int]
  rw [hθ, hL, map_smul, smul_eq_mul]
  simp only [mul_assoc]

/- English proof (translation)
Use `set u : B.U := ⟨B.ι z, B.memU z hz⟩ with hu`. Establish `hθz : s.θ (B.ι z) = B.ι z` using `by rw [s.comm, s.fix z hz]`. Establish `hc : B.ι z * s.θ (Quotient.out y) = s.θ (Quotient.out y) * B.ι z` using `(Subgroup.mem_center_iff.mp (B.cenG z hz) _).symm`. Establish `hk : s.ker f (δ * z) y = ((B.ω u)⁻¹ : ℂˣ) * s.ker f δ y`. Unfold `Base.Tw.ker`.

Establish `e : (Quotient.out y)⁻¹ * B.ι (δ * z) * s.θ (Quotient.out y) = ((Quotient.out y)⁻¹ * B.ι δ * s.θ (Quotient.out y)) * s.θ (u : G)`. Rewrite using `[map_mul, show (u : G) = B.ι z from rfl, hθz]`. Simplify using `only [mul_assoc, hc]`. Rewrite using `[e, hf.right]`. Establish `ht : LinearMap.trace ℂ V (B.W (δ * z) ∘ₗ s.Θ) = (B.ω u : ℂ) * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ)`.

Establish `hW : B.W (δ * z) ∘ₗ s.Θ = (B.ω u : ℂ) • (B.W δ ∘ₗ s.Θ)`. Use extensionality with `v`. Simplify using `only [LinearMap.comp_apply, map_mul, Module.End.mul_apply, B.scal z hz, LinearMap.smul_apply, map_smul]`. Both sides reduce to the same expression. Rewrite using `[hW, map_smul, smul_eq_mul]`.

Unfold `FF`. Rewrite using `[hk, ht, mul_mul_mul_comm, Units.inv_mul, one_mul]`.
-/
private theorem cusp_function_invariant (hf : s.IsTest f) (δ : Γ) (y : G ⧸ B.U) {z : Γ} (hz : z ∈ B.Γ₀) : FF s f (δ * z) y = FF s f δ y := by
  set u : B.U := ⟨B.ι z, B.memU z hz⟩ with hu
  have hθz : s.θ (B.ι z) = B.ι z := by rw [s.comm, s.fix z hz]
  have hc : B.ι z * s.θ (Quotient.out y) = s.θ (Quotient.out y) * B.ι z :=
    (Subgroup.mem_center_iff.mp (B.cenG z hz) _).symm
  have hk : s.ker f (δ * z) y = ((B.ω u)⁻¹ : ℂˣ) * s.ker f δ y := by
    unfold Base.Tw.ker
    have e : (Quotient.out y)⁻¹ * B.ι (δ * z) * s.θ (Quotient.out y) =
        ((Quotient.out y)⁻¹ * B.ι δ * s.θ (Quotient.out y)) * s.θ (u : G) := by
      rw [map_mul, show (u : G) = B.ι z from rfl, hθz]
      simp only [mul_assoc, hc]
    rw [e, hf.right]
  have ht : LinearMap.trace ℂ V (B.W (δ * z) ∘ₗ s.Θ) = (B.ω u : ℂ) * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ) := by
    have hW : B.W (δ * z) ∘ₗ s.Θ = (B.ω u : ℂ) • (B.W δ ∘ₗ s.Θ) := by
      ext v
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply, B.scal z hz, LinearMap.smul_apply, map_smul]
      rfl
    rw [hW, map_smul, smul_eq_mul]
  unfold FF
  rw [hk, ht, mul_mul_mul_comm, Units.inv_mul, one_mul]

/- English proof (translation)
Establish `hy : B.ι x • y = ((B.ι x * Quotient.out y : G) : G ⧸ B.U)` using `by conv_lhs => rw [← QuotientGroup.out_eq' y]`. Both sides reduce to the same expression. Rewrite using `[hy, ker_mk hf]`. Unfold `Base.Tw.ker`. Simplify using `only [mul_inv_rev, map_mul, map_inv, s.comm, mul_assoc]`.
-/
private theorem ker_conj (hf : s.IsTest f) (δ x : Γ) (y : G ⧸ B.U) : s.ker f δ (B.ι x • y) = s.ker f (x⁻¹ * δ * s.θΓ x) y := by
  have hy : B.ι x • y = ((B.ι x * Quotient.out y : G) : G ⧸ B.U) := by
    conv_lhs => rw [← QuotientGroup.out_eq' y]
    rfl
  rw [hy, ker_mk hf]
  unfold Base.Tw.ker
  simp only [mul_inv_rev, map_mul, map_inv, s.comm, mul_assoc]

/- English proof (translation)
Unfold `FF`. Rewrite using `[ker_conj hf]`. Use `congr 1`. Establish `e : B.W (x⁻¹ * δ * s.θΓ x) ∘ₗ s.Θ = B.W x⁻¹ * ((B.W δ ∘ₗ s.Θ) * B.W x)`. Use extensionality with `v`.

Simplify using `[map_mul, s.int]`. Rewrite using `[e, LinearMap.trace_mul_comm, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]`.
-/
private theorem FF_conj [FiniteDimensional ℂ V] (hf : s.IsTest f) (δ x : Γ) (y : G ⧸ B.U) :
    FF s f δ (B.ι x • y) = FF s f (x⁻¹ * δ * s.θΓ x) y := by
  unfold FF
  rw [ker_conj hf]
  congr 1
  have e : B.W (x⁻¹ * δ * s.θΓ x) ∘ₗ s.Θ = B.W x⁻¹ * ((B.W δ ∘ₗ s.Θ) * B.W x) := by
    ext v
    simp [map_mul, s.int]
  rw [e, LinearMap.trace_mul_comm, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

/- English proof (translation)
Use `letI := act B`. Use `haveI := normal0 B`. Establish `hle : B.Γ₀ ≤ s.Cent δ`. Introduce `z hz`. Use `show ∃ w ∈ B.Γ₀, z⁻¹ * δ * s.θΓ z = δ * w`.

Use `⟨1, B.Γ₀.one_mem, ?_⟩` and prove the remaining obligations. Rewrite using `[s.fix z hz, mul_one, mul_assoc, (Subgroup.mem_center_iff.mp (B.cenΓ hz) δ), inv_mul_cancel_left]`. Establish `hinv : ∀ h ∈ s.Cent δ, ∀ y : G ⧸ B.U, FF s f δ (h • y) = FF s f δ y`. Introduce `h hh y`. Take `⟨w, hw, hhw⟩` from `hh`.

Use `show FF s f δ (B.ι h • y) = _`. Rewrite using `[FF_conj hf, hhw, cusp_function_invariant hf δ y hw]`. Establish `hfin : {b : orbitRel.Quotient (s.Cent δ) (G ⧸ B.U) | FF s f δ (Quotient.out b) ≠ 0}.Finite`. Take `⟨S, hS⟩` from `centFin Γ G V B hB s f hf δ`. Use `(S.finite_toSet.image (fun g : G => (Quotient.mk'' ((g : G ⧸ B.U)) : orbitRel.Quotient (s.Cent δ) (G ⧸ B.U)))).subset ?_` and prove the remaining obligations.

Introduce `b hb`. Establish `hk : s.ker f δ (Quotient.out b) ≠ 0` using `fun h0 => hb (by unfold FF; rw [h0, zero_mul])`. Take `⟨t, s1, hs1, u, hu, hy⟩` from `hS _ hk`. Use `⟨s1, hs1, ?_⟩` and prove the remaining obligations. Rewrite using `[← Quotient.out_eq b]`.

Apply `Quotient.sound` to reduce the goal to its premises. Use `show (s1 : G ⧸ B.U) ∈ MulAction.orbit (s.Cent δ) (Quotient.out b)`. Use `⟨t⁻¹, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← QuotientGroup.out_eq' (Quotient.out b)]`. Use `show ((B.ι ((t⁻¹ : s.Cent δ) : Γ) * Quotient.out (Quotient.out b) : G) : G ⧸ B.U) = s1`.

Rewrite using `[hy]`. Apply `QuotientGroup.eq.mpr` to reduce the goal to its premises. Establish `e : (B.ι ((t⁻¹ : s.Cent δ) : Γ) * ((B.ι.comp (s.Cent δ).subtype) t * s1 * u))⁻¹ * s1 = u⁻¹`. Simplify using `[mul_assoc]`. Rewrite using `[e]`.

Conclude with `B.U.inv_mem hu`. Take `⟨-, hC⟩` from `countC B.Γ₀ (s.Cent δ) (triv0 B) hle (stab0 B hB) (FF s f δ) hinv hfin`. Establish `lhs : (fun a : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent δ) => (B.Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ * FF s f (a.2.out * δ * s.θΓ a.2.out⁻¹) a.1.out) = fun a => (B.Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • FF s f δ (a.2.out⁻¹ • a.1.out)`. Use function extensionality and compare the values at `a`. Rewrite using `[smul_eq_mul]`.

Use `congr 1`. Rewrite using `[show (a.2.out⁻¹ • a.1.out : G ⧸ B.U) = B.ι a.2.out⁻¹ • a.1.out from rfl, FF_conj hf, inv_inv]`. Rewrite using `[lhs, hC]`. Unfold `Base.Tw.term gqOn gq`. Rewrite using `[mul_comm, finsum_mul]`.

Apply `finsum_congr` to reduce the goal to its premises. Introduce `b`. Unfold `FF`. Rewrite using `[smul_eq_mul, div_eq_mul_inv]`. Establish `key : ∀ n m : ℕ, n = m → s.ker f δ (Quotient.out b) * (n : ℂ)⁻¹ * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ) = (m : ℂ)⁻¹ * (s.ker f δ (Quotient.out b) * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ))`.

Introduce `n m h`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Apply `key` to reduce the goal to its premises. Rewrite using `[← Subgroup.relIndex_subgroupOf inf_le_left, Subgroup.inf_subgroupOf_left]`.

Use `congr 1`.
-/
private theorem termC [FiniteDimensional ℂ V] (hB : B.Fin) (hf : s.IsTest f) (δ : Γ) : letI := act B
    s.term f δ = ∑ᶠ a : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent δ),
      (B.Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ * FF s f (a.2.out * δ * s.θΓ a.2.out⁻¹) a.1.out := by
  letI := act B
  haveI := normal0 B
  have hle : B.Γ₀ ≤ s.Cent δ := by
    intro z hz
    show ∃ w ∈ B.Γ₀, z⁻¹ * δ * s.θΓ z = δ * w
    refine ⟨1, B.Γ₀.one_mem, ?_⟩
    rw [s.fix z hz, mul_one, mul_assoc, (Subgroup.mem_center_iff.mp (B.cenΓ hz) δ), inv_mul_cancel_left]
  have hinv : ∀ h ∈ s.Cent δ, ∀ y : G ⧸ B.U, FF s f δ (h • y) = FF s f δ y := by
    intro h hh y
    obtain ⟨w, hw, hhw⟩ := hh
    show FF s f δ (B.ι h • y) = _
    rw [FF_conj hf, hhw, cusp_function_invariant hf δ y hw]
  have hfin : {b : orbitRel.Quotient (s.Cent δ) (G ⧸ B.U) | FF s f δ (Quotient.out b) ≠ 0}.Finite := by
    obtain ⟨S, hS⟩ := centFin Γ G V B hB s f hf δ
    refine (S.finite_toSet.image (fun g : G =>
      (Quotient.mk'' ((g : G ⧸ B.U)) : orbitRel.Quotient (s.Cent δ) (G ⧸ B.U)))).subset ?_
    intro b hb
    have hk : s.ker f δ (Quotient.out b) ≠ 0 := fun h0 => hb (by unfold FF; rw [h0, zero_mul])
    obtain ⟨t, s1, hs1, u, hu, hy⟩ := hS _ hk
    refine ⟨s1, hs1, ?_⟩
    rw [← Quotient.out_eq b]
    apply Quotient.sound
    show (s1 : G ⧸ B.U) ∈ MulAction.orbit (s.Cent δ) (Quotient.out b)
    refine ⟨t⁻¹, ?_⟩
    conv_lhs => rw [← QuotientGroup.out_eq' (Quotient.out b)]
    show ((B.ι ((t⁻¹ : s.Cent δ) : Γ) * Quotient.out (Quotient.out b) : G) : G ⧸ B.U) = s1
    rw [hy]
    apply QuotientGroup.eq.mpr
    have e : (B.ι ((t⁻¹ : s.Cent δ) : Γ) * ((B.ι.comp (s.Cent δ).subtype) t * s1 * u))⁻¹ * s1 = u⁻¹ := by
      simp [mul_assoc]
    rw [e]
    exact B.U.inv_mem hu
  obtain ⟨-, hC⟩ := countC B.Γ₀ (s.Cent δ) (triv0 B) hle (stab0 B hB) (FF s f δ) hinv hfin
  have lhs : (fun a : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent δ) =>
      (B.Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ * FF s f (a.2.out * δ * s.θΓ a.2.out⁻¹) a.1.out) =
      fun a => (B.Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • FF s f δ (a.2.out⁻¹ • a.1.out) := by
    funext a
    rw [smul_eq_mul]
    congr 1
    rw [show (a.2.out⁻¹ • a.1.out : G ⧸ B.U) = B.ι a.2.out⁻¹ • a.1.out from rfl, FF_conj hf, inv_inv]
  rw [lhs, hC]
  unfold Base.Tw.term gqOn gq
  rw [mul_comm, finsum_mul]
  apply finsum_congr
  intro b
  unfold FF
  rw [smul_eq_mul, div_eq_mul_inv]
  have key : ∀ n m : ℕ, n = m → s.ker f δ (Quotient.out b) * (n : ℂ)⁻¹ * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ) =
      (m : ℂ)⁻¹ * (s.ker f δ (Quotient.out b) * LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ)) := by
    intro n m h
    rw [h]
    ring
  apply key
  rw [← Subgroup.relIndex_subgroupOf inf_le_left, Subgroup.inf_subgroupOf_left]
  congr 1

end

/- English proof (translation)
Establish `hθz : s.θ (B.ι z) = B.ι z` using `by rw [s.comm, s.fix z hz]`. Establish `hc : B.ι z * s.θ (Quotient.out y) = s.θ (Quotient.out y) * B.ι z` using `(Subgroup.mem_center_iff.mp (B.cenG z hz) _).symm`. Unfold `Base.Tw.ker`. Establish `e : (Quotient.out y)⁻¹ * B.ι (ε * z) * s.θ (Quotient.out y) = ((Quotient.out y)⁻¹ * B.ι ε * s.θ (Quotient.out y)) * s.θ ((⟨B.ι z, B.memU z hz⟩ : B.U) : G)`. Rewrite using `[map_mul, show ((⟨B.ι z, B.memU z hz⟩ : B.U) : G) = B.ι z from rfl, hθz]`.

Simplify using `only [mul_assoc, hc]`. Rewrite using `[e, hf.right]`.
-/
private theorem trace_mul_re_nonneg_of_posSemidef {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]
    {B : Base Γ G V} {s : B.Tw} {f : G → ℂ} (hf : s.IsTest f) (ε : Γ) (y : G ⧸ B.U) {z : Γ}
    (hz : z ∈ B.Γ₀) : s.ker f (ε * z) y = ((B.ω ⟨B.ι z, B.memU z hz⟩)⁻¹ : ℂˣ) * s.ker f ε y := by
  have hθz : s.θ (B.ι z) = B.ι z := by rw [s.comm, s.fix z hz]
  have hc : B.ι z * s.θ (Quotient.out y) = s.θ (Quotient.out y) * B.ι z :=
    (Subgroup.mem_center_iff.mp (B.cenG z hz) _).symm
  unfold Base.Tw.ker
  have e : (Quotient.out y)⁻¹ * B.ι (ε * z) * s.θ (Quotient.out y) =
      ((Quotient.out y)⁻¹ * B.ι ε * s.θ (Quotient.out y)) * s.θ ((⟨B.ι z, B.memU z hz⟩ : B.U) : G) := by
    rw [map_mul, show ((⟨B.ι z, B.memU z hz⟩ : B.U) : G) = B.ι z from rfl, hθz]
    simp only [mul_assoc, hc]
  rw [e, hf.right]

/- English proof (translation)
Take `⟨c, hc⟩` from `QuotientGroup.mk_out_eq_mul (s.Cent δ₀) x`. Take `⟨z, hz, hcz⟩` from `c.2`. Establish `hzc : ∀ g : Γ, g * z⁻¹ = z⁻¹ * g` using `fun g => Subgroup.mem_center_iff.mp (B.cenΓ (B.Γ₀.inv_mem hz)) g`. Use `⟨z⁻¹, B.Γ₀.inv_mem hz, ?_⟩` and prove the remaining obligations. Establish `key : (c : Γ) * δ₀ * s.θΓ (c : Γ)⁻¹ = δ₀ * z⁻¹`.

Rewrite using `[map_inv, mul_inv_eq_iff_eq_mul]`. Establish `h1 : δ₀ * s.θΓ c = c * (δ₀ * z)`. Rewrite using `[← hcz]`. Use `group`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hc]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_inv_rev, map_mul]`. Use `group`. Use `_ = x * δ₀ * s.θΓ x⁻¹ * z⁻¹ := by`.

Rewrite using `[key]`. Simplify using `only [mul_assoc, hzc (s.θΓ x⁻¹)]`.
-/
private theorem sum_phi_add_star_eq_trace {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]
    {B : Base Γ G V} (s : B.Tw) (δ₀ x : Γ) :
    ∃ w ∈ B.Γ₀, Quotient.out (x : Γ ⧸ s.Cent δ₀) * δ₀ * s.θΓ (Quotient.out (x : Γ ⧸ s.Cent δ₀))⁻¹ =
      x * δ₀ * s.θΓ x⁻¹ * w := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (s.Cent δ₀) x
  obtain ⟨z, hz, hcz⟩ := c.2
  have hzc : ∀ g : Γ, g * z⁻¹ = z⁻¹ * g := fun g =>
    Subgroup.mem_center_iff.mp (B.cenΓ (B.Γ₀.inv_mem hz)) g
  refine ⟨z⁻¹, B.Γ₀.inv_mem hz, ?_⟩
  have key : (c : Γ) * δ₀ * s.θΓ (c : Γ)⁻¹ = δ₀ * z⁻¹ := by
    rw [map_inv, mul_inv_eq_iff_eq_mul]
    have h1 : δ₀ * s.θΓ c = c * (δ₀ * z) := by
      rw [← hcz]
      group
    calc (c : Γ) * δ₀ = c * (δ₀ * z) * z⁻¹ := by group
      _ = δ₀ * s.θΓ c * z⁻¹ := by rw [h1]
      _ = δ₀ * z⁻¹ * s.θΓ c := by rw [mul_assoc, hzc, ← mul_assoc]
  rw [hc]
  calc x * (c : Γ) * δ₀ * s.θΓ (x * c)⁻¹ = x * ((c : Γ) * δ₀ * s.θΓ (c : Γ)⁻¹) * s.θΓ x⁻¹ := by
        rw [mul_inv_rev, map_mul]
        group
    _ = x * δ₀ * s.θΓ x⁻¹ * z⁻¹ := by
        rw [key]
        simp only [mul_assoc, hzc (s.θΓ x⁻¹)]

/- English proof (translation)
Introduce `Γ G V _ _ _ _ _ B hB s f hf I δ hinj hcov`. Use `letI := act B`. Use `haveI := finQ B hB`. Establish `hHD : HD s f` using `finD B hB s f hf`. Establish `hzc : ∀ z ∈ B.Γ₀, ∀ g : Γ, g * z = z * g` using `fun z hz g => Subgroup.mem_center_iff.mp (B.cenΓ hz) g`.

Set `e : (i : I) → Γ ⧸ s.Cent (δ i) → Γ` to `fun i a => Quotient.out a * δ i * s.θΓ (Quotient.out a)⁻¹`. Set `m : (Σ i : I, orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))) → orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀)` to `fun p => (p.2.1, (((s.θΓ.symm (e p.1 p.2.2))⁻¹ : Γ) : Γ ⧸ B.Γ₀))`. Set `ε : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) → Γ` to `fun b => s.θΓ (Quotient.out b.2)⁻¹`. Establish `K1 : ∀ p, ∃ w ∈ B.Γ₀, ε (m p) = e p.1 p.2.2 * w`. Introduce `p`.

Take `⟨w, hw⟩` from `QuotientGroup.mk_out_eq_mul B.Γ₀ ((s.θΓ.symm (e p.1 p.2.2))⁻¹)`. Use `⟨(w : Γ)⁻¹, B.Γ₀.inv_mem w.2, ?_⟩` and prove the remaining obligations. Use `show s.θΓ (Quotient.out ((((s.θΓ.symm (e p.1 p.2.2))⁻¹ : Γ)) : Γ ⧸ B.Γ₀))⁻¹ = _`. Rewrite using `[hw, mul_inv_rev, inv_inv, map_mul, MulEquiv.apply_symm_apply, map_inv, s.fix _ w.2]`. Conclude with `(hzc _ (B.Γ₀.inv_mem w.2) _).symm`.

Establish `Minj : Function.Injective m`. Introduce and unpack `⟨i, o, a⟩ ⟨i', o', a'⟩ h`. Establish `ho : o = o'` using `congrArg Prod.fst h`. Establish `ha : (((s.θΓ.symm (e i a))⁻¹ : Γ) : Γ ⧸ B.Γ₀) = (((s.θΓ.symm (e i' a'))⁻¹ : Γ) : Γ ⧸ B.Γ₀)` using `congrArg Prod.snd h`. Establish `hu : s.θΓ.symm (e i a) * (s.θΓ.symm (e i' a'))⁻¹ ∈ B.Γ₀`.

Use `QuotientGroup.eq.mp ha` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Establish `hfix` using `s.fix _ hu`. Rewrite `hfix` using `[map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz, hEz⟩ : ∃ z ∈ B.Γ₀, e i' a' = e i a * z := by`.

Use `⟨(s.θΓ.symm (e i a) * (s.θΓ.symm (e i' a'))⁻¹)⁻¹, B.Γ₀.inv_mem hu, ?_⟩` and prove the remaining obligations. Rewrite using `[hzc _ (B.Γ₀.inv_mem hu) (e i a), ← hfix]`. Use `group`. Establish `h2 : Quotient.out a' * δ i' * s.θΓ (Quotient.out a')⁻¹ = Quotient.out a * δ i * s.θΓ (Quotient.out a)⁻¹ * z` using `hEz`. Establish `gen : ∀ d d' q q' : Γ, q' * d' * s.θΓ q'⁻¹ = q * d * s.θΓ q⁻¹ * z → d' = (q⁻¹ * q')⁻¹ * d * s.θΓ (q⁻¹ * q') * z`.

Introduce `d d' q q' hq`. Establish `h3 : d' = q'⁻¹ * (q * d * s.θΓ q⁻¹ * z) * s.θΓ q'`. Rewrite using `[← hq, map_inv]`. Use `group`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h3, map_inv]`. Use `group`. Use `_ = q'⁻¹ * (q * d * (s.θΓ q)⁻¹) * (s.θΓ q' * z) := by rw [← hzc z hz (s.θΓ q')]`. Use `_ = _ := by`. Rewrite using `[map_mul, map_inv]`.

Use `group`. Establish `hx` using `gen _ _ _ _ h2`. Establish `hii` using `hinj i i' ⟨_, z, hz, hx⟩`. Substitute `hii` using the available equality. Establish `hcent : (Quotient.out a)⁻¹ * Quotient.out a' ∈ s.Cent (δ i)` using `⟨z⁻¹, B.Γ₀.inv_mem hz, eq_mul_inv_of_mul_eq hx.symm⟩`.

Establish `haa : a = a'`. Rewrite using `[← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' a']`. Conclude with `QuotientGroup.eq.mpr hcent`. Rewrite using `[ho, haa]`. Set `F' : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) → ℂ` to `fun b => (B.Γ₀.relIndex (stabilizer Γ (Quotient.out b.1)) : ℂ)⁻¹ * LinearMap.trace ℂ V (Tk s f (Quotient.out (Quotient.out b.1)) (Quotient.out (Quotient.out b.1)) (Quotient.out b.2)⁻¹)`.

Set `F : (Σ i : I, orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))) → ℂ` to `fun p => (B.Γ₀.relIndex (stabilizer Γ (Quotient.out p.2.1)) : ℂ)⁻¹ * FF s f (e p.1 p.2.2) (Quotient.out p.2.1)`. Establish `hF'FF : ∀ b, F' b = (B.Γ₀.relIndex (stabilizer Γ (Quotient.out b.1)) : ℂ)⁻¹ * FF s f (ε b) (Quotient.out b.1)`. Introduce `b`. Use `show _ * _ = _ * FF s f (s.θΓ (Quotient.out b.2)⁻¹) _`. Rewrite using `[FF_tr, MulEquiv.symm_apply_apply]`.

Establish `hFeq : ∀ p, F p = ((((fun _ => 1) : _ → ℕ) (m p) : ℕ) : ℂ)⁻¹ • F' (m p)`. Introduce `p`. Rewrite using `[Nat.cast_one, inv_one, one_smul, hF'FF]`. Take `⟨w, hw, hwe⟩` from `K1 p`. Rewrite using `[hwe, cusp_function_invariant hf _ _ hw]`.

Establish `hKfin : {b : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) | s.ker f (ε b) (Quotient.out b.1) ≠ 0}.Finite`. Use `(Set.finite_iUnion (fun o : orbitRel.Quotient Γ (G ⧸ B.U) => (Set.finite_singleton o).prod (f_fin hHD (Quotient.out (Quotient.out o)) (Quotient.out (Quotient.out o))))).subset ?_` and prove the remaining obligations. Introduce and unpack `⟨o, x⟩ hb`. Establish `hb' : f ((Quotient.out (Quotient.out o))⁻¹ * B.ι (s.θΓ (Quotient.out x)⁻¹) * s.θ (Quotient.out (Quotient.out o))) ≠ 0` using `hb`. Use `Set.mem_iUnion.mpr ⟨o, Set.mem_singleton o, ?_⟩` and prove the remaining obligations.

Use `show f _ ≠ 0`. Use `hb' using 2` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul, s.comm, mul_assoc]`. Establish `hF'fin : (Function.support F').Finite` using `hKfin.subset (fun b hb h0 => hb (by`. Rewrite using `[hF'FF]`.

Unfold `FF`. Rewrite using `[h0]`. Use the proof step `ring))`. Establish `Msurj : ∀ b, s.ker f (ε b) (Quotient.out b.1) ≠ 0 → ∃ p, m p = b`. Introduce and unpack `⟨o, x⟩ hb`.

Take `⟨i, y, z, hz, hy⟩` from `hcov _ ⟨_, hb⟩`. Use `⟨⟨i, o, ((y⁻¹ : Γ) : Γ ⧸ s.Cent (δ i))⟩, ?_⟩` and prove the remaining obligations. Take `⟨w, hw, hwe⟩` from `sum_phi_add_star_eq_trace s (δ i) y⁻¹`. Establish `hy' : s.θΓ (Quotient.out x)⁻¹ = y⁻¹ * δ i * s.θΓ y * z` using `hy`. Establish `hE : e i ((y⁻¹ : Γ) : Γ ⧸ s.Cent (δ i)) = s.θΓ (Quotient.out x)⁻¹ * (z⁻¹ * w)` using `by show Quotient.out _ * δ i * s.θΓ (Quotient.out _)⁻¹ = _`.

Rewrite using `[hwe, inv_inv, hy']`. Use `group`. Establish `hsym : ∀ q ∈ B.Γ₀, s.θΓ.symm q = q` using `fun q hq => (MulEquiv.symm_apply_eq _).mpr (s.fix q hq).symm`. Establish `hzw : z⁻¹ * w ∈ B.Γ₀` using `B.Γ₀.mul_mem (B.Γ₀.inv_mem hz) hw`. Use `Prod.ext rfl ?_` and prove the remaining obligations.

Use `show (((s.θΓ.symm (e i ((y⁻¹ : Γ) : Γ ⧸ s.Cent (δ i))))⁻¹ : Γ) : Γ ⧸ B.Γ₀) = x`. Rewrite using `[← QuotientGroup.out_eq' x, QuotientGroup.eq, inv_inv, hE, map_mul, MulEquiv.symm_apply_apply, hsym _ hzw, mul_assoc, ← hzc _ hzw (Quotient.out x), ← mul_assoc, inv_mul_cancel, one_mul]`. Conclude with `hzw`. Establish `hcard : ∀ b, F' b ≠ 0 → ((fun _ => 1) : _ → ℕ) b ≠ 0 ∧ Nat.card {p // m p = b} = ((fun _ => 1) : _ → ℕ) b`. Introduce `b hb`.

Use `⟨one_ne_zero, Nat.card_eq_one_iff_unique.mpr ⟨⟨fun p q => Subtype.ext (Minj (p.2.trans q.2.symm))⟩, ?_⟩⟩` and prove the remaining obligations. Establish `hk : s.ker f (ε b) (Quotient.out b.1) ≠ 0` using `fun h0 => hb (by`. Rewrite using `[hF'FF]`. Unfold `FF`. Rewrite using `[h0]`.

Use the proof step `ring)`. Take `⟨p, hp⟩` from `Msurj b hk`. Conclude with `⟨⟨p, hp⟩⟩`. Take `⟨hFfin, hsum⟩` from `sum_fib m F F' (fun _ => 1) hF'fin hcard hFeq`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `hP : {p : (Σ i : I, orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))) | s.ker f (e p.1 p.2.2) (Quotient.out p.2.1) ≠ 0} ⊆ m ⁻¹' {b | s.ker f (ε b) (Quotient.out b.1) ≠ 0}`. Introduce `p hp`. Take `⟨w, hw, hwe⟩` from `K1 p`. Use `show s.ker f (ε (m p)) (Quotient.out (m p).1) ≠ 0`. Rewrite using `[hwe, trace_mul_re_nonneg_of_posSemidef hf _ _ hw]`.

Conclude with `mul_ne_zero (Units.ne_zero _) hp`. Establish `hPfin` using `(hKfin.preimage Minj.injOn).subset hP`. Use `(hPfin.image Sigma.fst).subset ?_` and prove the remaining obligations. Introduce and unpack `i ⟨y, hy⟩`. Take `⟨g, hg⟩ : ∃ g : Γ, g • y = Quotient.out (Quotient.mk'' y : orbitRel.Quotient Γ (G ⧸ B.U))` from `Quotient.mk_out (s := orbitRel Γ (G ⧸ B.U)) y`.

Use `⟨⟨i, (Quotient.mk'' y : orbitRel.Quotient Γ (G ⧸ B.U)), ((g : Γ) : Γ ⧸ s.Cent (δ i))⟩, ?_, rfl⟩` and prove the remaining obligations. Take `⟨w, hw, hwe⟩` from `sum_phi_add_star_eq_trace s (δ i) g`. Use `show s.ker f (e i ((g : Γ) : Γ ⧸ s.Cent (δ i))) (Quotient.out (Quotient.mk'' y : orbitRel.Quotient Γ (G ⧸ B.U))) ≠ 0`. Rewrite using `[show e i ((g : Γ) : Γ ⧸ s.Cent (δ i)) = _ from hwe, trace_mul_re_nonneg_of_posSemidef hf _ _ hw]`. Use `mul_ne_zero (Units.ne_zero _) ?_` and prove the remaining obligations.

Rewrite using `[← hg, show g • y = B.ι g • y from rfl, ker_conj hf]`. Use `hy using 2` and compare the differences between its conclusion and the goal. Rewrite using `[map_inv]`. Use `group`. Rewrite using `[traceA hB hf hHD]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Z.Sym.Tf.trace :
    UpperTheory.V.Z.Sym.Tf.Trace := by
  intro Γ G V _ _ _ _ _ B hB s f hf I δ hinj hcov
  letI := act B
  haveI := finQ B hB
  have hHD : HD s f := finD B hB s f hf
  have hzc : ∀ z ∈ B.Γ₀, ∀ g : Γ, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp (B.cenΓ hz) g
  let e : (i : I) → Γ ⧸ s.Cent (δ i) → Γ := fun i a => Quotient.out a * δ i * s.θΓ (Quotient.out a)⁻¹
  let m : (Σ i : I, orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))) →
      orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) :=
    fun p => (p.2.1, (((s.θΓ.symm (e p.1 p.2.2))⁻¹ : Γ) : Γ ⧸ B.Γ₀))
  let ε : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) → Γ := fun b => s.θΓ (Quotient.out b.2)⁻¹
  have K1 : ∀ p, ∃ w ∈ B.Γ₀, ε (m p) = e p.1 p.2.2 * w := by
    intro p
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul B.Γ₀ ((s.θΓ.symm (e p.1 p.2.2))⁻¹)
    refine ⟨(w : Γ)⁻¹, B.Γ₀.inv_mem w.2, ?_⟩
    show s.θΓ (Quotient.out ((((s.θΓ.symm (e p.1 p.2.2))⁻¹ : Γ)) : Γ ⧸ B.Γ₀))⁻¹ = _
    rw [hw, mul_inv_rev, inv_inv, map_mul, MulEquiv.apply_symm_apply, map_inv, s.fix _ w.2]
    exact (hzc _ (B.Γ₀.inv_mem w.2) _).symm
  have Minj : Function.Injective m := by
    rintro ⟨i, o, a⟩ ⟨i', o', a'⟩ h
    have ho : o = o' := congrArg Prod.fst h
    have ha : (((s.θΓ.symm (e i a))⁻¹ : Γ) : Γ ⧸ B.Γ₀) = (((s.θΓ.symm (e i' a'))⁻¹ : Γ) : Γ ⧸ B.Γ₀) :=
      congrArg Prod.snd h
    have hu : s.θΓ.symm (e i a) * (s.θΓ.symm (e i' a'))⁻¹ ∈ B.Γ₀ := by
      have := QuotientGroup.eq.mp ha
      rwa [inv_inv] at this
    have hfix := s.fix _ hu
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hfix
    obtain ⟨z, hz, hEz⟩ : ∃ z ∈ B.Γ₀, e i' a' = e i a * z := by
      refine ⟨(s.θΓ.symm (e i a) * (s.θΓ.symm (e i' a'))⁻¹)⁻¹, B.Γ₀.inv_mem hu, ?_⟩
      rw [hzc _ (B.Γ₀.inv_mem hu) (e i a), ← hfix]
      group
    have h2 : Quotient.out a' * δ i' * s.θΓ (Quotient.out a')⁻¹ =
        Quotient.out a * δ i * s.θΓ (Quotient.out a)⁻¹ * z := hEz
    have gen : ∀ d d' q q' : Γ, q' * d' * s.θΓ q'⁻¹ = q * d * s.θΓ q⁻¹ * z →
        d' = (q⁻¹ * q')⁻¹ * d * s.θΓ (q⁻¹ * q') * z := by
      intro d d' q q' hq
      have h3 : d' = q'⁻¹ * (q * d * s.θΓ q⁻¹ * z) * s.θΓ q' := by
        rw [← hq, map_inv]
        group
      calc d' = q'⁻¹ * (q * d * (s.θΓ q)⁻¹) * (z * s.θΓ q') := by
            rw [h3, map_inv]
            group
        _ = q'⁻¹ * (q * d * (s.θΓ q)⁻¹) * (s.θΓ q' * z) := by rw [← hzc z hz (s.θΓ q')]
        _ = _ := by
            rw [map_mul, map_inv]
            group
    have hx := gen _ _ _ _ h2
    have hii := hinj i i' ⟨_, z, hz, hx⟩
    subst hii
    have hcent : (Quotient.out a)⁻¹ * Quotient.out a' ∈ s.Cent (δ i) :=
      ⟨z⁻¹, B.Γ₀.inv_mem hz, eq_mul_inv_of_mul_eq hx.symm⟩
    have haa : a = a' := by
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' a']
      exact QuotientGroup.eq.mpr hcent
    rw [ho, haa]
  let F' : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) → ℂ := fun b =>
    (B.Γ₀.relIndex (stabilizer Γ (Quotient.out b.1)) : ℂ)⁻¹ *
      LinearMap.trace ℂ V (Tk s f (Quotient.out (Quotient.out b.1)) (Quotient.out (Quotient.out b.1))
        (Quotient.out b.2)⁻¹)
  let F : (Σ i : I, orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))) → ℂ := fun p =>
    (B.Γ₀.relIndex (stabilizer Γ (Quotient.out p.2.1)) : ℂ)⁻¹ * FF s f (e p.1 p.2.2) (Quotient.out p.2.1)
  have hF'FF : ∀ b, F' b = (B.Γ₀.relIndex (stabilizer Γ (Quotient.out b.1)) : ℂ)⁻¹ *
      FF s f (ε b) (Quotient.out b.1) := by
    intro b
    show _ * _ = _ * FF s f (s.θΓ (Quotient.out b.2)⁻¹) _
    rw [FF_tr, MulEquiv.symm_apply_apply]
  have hFeq : ∀ p, F p = ((((fun _ => 1) : _ → ℕ) (m p) : ℕ) : ℂ)⁻¹ • F' (m p) := by
    intro p
    rw [Nat.cast_one, inv_one, one_smul, hF'FF]
    obtain ⟨w, hw, hwe⟩ := K1 p
    rw [hwe, cusp_function_invariant hf _ _ hw]
  have hKfin : {b : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ B.Γ₀) | s.ker f (ε b) (Quotient.out b.1) ≠ 0}.Finite := by
    refine (Set.finite_iUnion (fun o : orbitRel.Quotient Γ (G ⧸ B.U) =>
      (Set.finite_singleton o).prod (f_fin hHD (Quotient.out (Quotient.out o)) (Quotient.out (Quotient.out o))))).subset ?_
    rintro ⟨o, x⟩ hb
    have hb' : f ((Quotient.out (Quotient.out o))⁻¹ * B.ι (s.θΓ (Quotient.out x)⁻¹) *
        s.θ (Quotient.out (Quotient.out o))) ≠ 0 := hb
    refine Set.mem_iUnion.mpr ⟨o, Set.mem_singleton o, ?_⟩
    show f _ ≠ 0
    convert hb' using 2
    rw [map_mul, s.comm, mul_assoc]
  have hF'fin : (Function.support F').Finite := hKfin.subset (fun b hb h0 => hb (by
    rw [hF'FF]
    unfold FF
    rw [h0]
    ring))
  have Msurj : ∀ b, s.ker f (ε b) (Quotient.out b.1) ≠ 0 → ∃ p, m p = b := by
    rintro ⟨o, x⟩ hb
    obtain ⟨i, y, z, hz, hy⟩ := hcov _ ⟨_, hb⟩
    refine ⟨⟨i, o, ((y⁻¹ : Γ) : Γ ⧸ s.Cent (δ i))⟩, ?_⟩
    obtain ⟨w, hw, hwe⟩ := sum_phi_add_star_eq_trace s (δ i) y⁻¹
    have hy' : s.θΓ (Quotient.out x)⁻¹ = y⁻¹ * δ i * s.θΓ y * z := hy
    have hE : e i ((y⁻¹ : Γ) : Γ ⧸ s.Cent (δ i)) = s.θΓ (Quotient.out x)⁻¹ * (z⁻¹ * w) := by
      show Quotient.out _ * δ i * s.θΓ (Quotient.out _)⁻¹ = _
      rw [hwe, inv_inv, hy']
      group
    have hsym : ∀ q ∈ B.Γ₀, s.θΓ.symm q = q := fun q hq =>
      (MulEquiv.symm_apply_eq _).mpr (s.fix q hq).symm
    have hzw : z⁻¹ * w ∈ B.Γ₀ := B.Γ₀.mul_mem (B.Γ₀.inv_mem hz) hw
    refine Prod.ext rfl ?_
    show (((s.θΓ.symm (e i ((y⁻¹ : Γ) : Γ ⧸ s.Cent (δ i))))⁻¹ : Γ) : Γ ⧸ B.Γ₀) = x
    rw [← QuotientGroup.out_eq' x, QuotientGroup.eq, inv_inv, hE, map_mul, MulEquiv.symm_apply_apply,
      hsym _ hzw, mul_assoc, ← hzc _ hzw (Quotient.out x), ← mul_assoc, inv_mul_cancel, one_mul]
    exact hzw
  have hcard : ∀ b, F' b ≠ 0 → ((fun _ => 1) : _ → ℕ) b ≠ 0 ∧
      Nat.card {p // m p = b} = ((fun _ => 1) : _ → ℕ) b := by
    intro b hb
    refine ⟨one_ne_zero, Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun p q => Subtype.ext (Minj (p.2.trans q.2.symm))⟩, ?_⟩⟩
    have hk : s.ker f (ε b) (Quotient.out b.1) ≠ 0 := fun h0 => hb (by
      rw [hF'FF]
      unfold FF
      rw [h0]
      ring)
    obtain ⟨p, hp⟩ := Msurj b hk
    exact ⟨⟨p, hp⟩⟩
  obtain ⟨hFfin, hsum⟩ := sum_fib m F F' (fun _ => 1) hF'fin hcard hFeq
  refine ⟨?_, ?_⟩
  · have hP : {p : (Σ i : I, orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))) |
        s.ker f (e p.1 p.2.2) (Quotient.out p.2.1) ≠ 0} ⊆
        m ⁻¹' {b | s.ker f (ε b) (Quotient.out b.1) ≠ 0} := by
      intro p hp
      obtain ⟨w, hw, hwe⟩ := K1 p
      show s.ker f (ε (m p)) (Quotient.out (m p).1) ≠ 0
      rw [hwe, trace_mul_re_nonneg_of_posSemidef hf _ _ hw]
      exact mul_ne_zero (Units.ne_zero _) hp
    have hPfin := (hKfin.preimage Minj.injOn).subset hP
    refine (hPfin.image Sigma.fst).subset ?_
    rintro i ⟨y, hy⟩
    obtain ⟨g, hg⟩ : ∃ g : Γ, g • y = Quotient.out (Quotient.mk'' y : orbitRel.Quotient Γ (G ⧸ B.U)) :=
      Quotient.mk_out (s := orbitRel Γ (G ⧸ B.U)) y
    refine ⟨⟨i, (Quotient.mk'' y : orbitRel.Quotient Γ (G ⧸ B.U)), ((g : Γ) : Γ ⧸ s.Cent (δ i))⟩, ?_, rfl⟩
    obtain ⟨w, hw, hwe⟩ := sum_phi_add_star_eq_trace s (δ i) g
    show s.ker f (e i ((g : Γ) : Γ ⧸ s.Cent (δ i))) (Quotient.out (Quotient.mk'' y : orbitRel.Quotient Γ (G ⧸ B.U))) ≠ 0
    rw [show e i ((g : Γ) : Γ ⧸ s.Cent (δ i)) = _ from hwe, trace_mul_re_nonneg_of_posSemidef hf _ _ hw]
    refine mul_ne_zero (Units.ne_zero _) ?_
    rw [← hg, show g • y = B.ι g • y from rfl, ker_conj hf]
    convert hy using 2
    rw [map_inv]
    group
  · rw [traceA hB hf hHD]
    calc _ = ∑ᶠ (a : orbitRel.Quotient Γ (G ⧸ B.U)) (b : Γ ⧸ B.Γ₀), F' (a, b) := rfl
      _ = ∑ᶠ ab, F' ab := (finsum_curry F' hF'fin).symm
      _ = ∑ᶠ p, F p := hsum.symm
      _ = ∑ᶠ (i : I) (q : orbitRel.Quotient Γ (G ⧸ B.U) × (Γ ⧸ s.Cent (δ i))), F ⟨i, q⟩ := finsum_sig F hFfin
      _ = ∑ᶠ i, s.term f (δ i) := finsum_congr fun i => (termC hB hf (δ i)).symm
