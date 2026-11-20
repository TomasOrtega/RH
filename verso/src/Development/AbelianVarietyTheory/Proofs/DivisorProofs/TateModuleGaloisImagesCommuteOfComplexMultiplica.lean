import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeFiniteFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentNumberFieldEndomorphismsTateModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemSpanOrbitOfNumberFieldLatticeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMComm

/- English proof (translation)
Use `set P := Submodule.span ℤ_[l] (Set.range ρ) with hP`. Establish `hcen : ∀ k : Module.End ℤ_[l] T, (∀ a, k * ρ a = ρ a * k) → ∀ x ∈ P, k * x = x * k`. Introduce `k hk x hx`. Establish `: P ≤ Subalgebra.toSubmodule (Subalgebra.centralizer ℤ_[l] {k})`. Rewrite using `[hP, Submodule.span_le]`.

Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]`. Introduce and unpack `_ rfl`. Conclude with `hk a`. Establish `h1` using `this hx`.

Rewrite `h1` using `[Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]`. Conclude with `h1 k rfl`. Establish `hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x`. Introduce `x hx y hy`. Establish `hx' : ∀ a, x * ρ a = ρ a * x` using `fun a => by`.

Use `hcen (ρ a) (fun b => by rw [← map_mul, ← map_mul, mul_comm]) x hx` as an intermediate fact. Conclude with `this.symm`. Conclude with `hcen x hx' y hy`. Establish `hev : ∀ w : T, ∃ x ∈ P, x v = c • w`. Introduce `w`.

Use `hv w` as an intermediate fact. Rewrite using `[show (Set.range fun a => ρ a v) = (LinearMap.applyₗ v : Module.End ℤ_[l] T →ₗ[ℤ_[l]] T) '' Set.range ρ by`. Rewrite using `[← Set.range_comp]`. Use the proof step `rfl, Submodule.span_image] at this`. Take `⟨x, hx, e⟩` from `this`.

Conclude with `⟨x, hx, e⟩`. Use `LinearMap.ext fun t => ?_` and prove the remaining obligations. Take `⟨x, hx, ex⟩` from `hev t`. Take `⟨y, hy, ey⟩` from `hev (g v)`. Take `⟨z, hz, ez⟩` from `hev (h v)`.

Establish `hgx` using `hcen g hg x hx`. Establish `hhx` using `hcen h hh x hx`. Establish `k1 : c • c • c • (g * h) t = x (z (y v))`. Establish `e1 : c • (g * h) t = x (g (h v))`. Rewrite using `[← map_smul, ← ex, Module.End.mul_apply]`.

Express the relevant statement in the definitionally equal form `(g * (h * x)) v = x (g (h v))`. Rewrite using `[hhx, ← _root_.mul_assoc, hgx, _root_.mul_assoc]`. Both sides reduce to the same expression. Establish `e2 : c • x (g (h v)) = x (z (g v))`. Rewrite using `[← map_smul, ← map_smul, ← ez]`.

Express the relevant statement in the definitionally equal form `x ((g * z) v) = x ((z * g) v)`. Rewrite using `[hcen g hg z hz]`. Rewrite using `[e1, e2, ← map_smul, ← map_smul, ← ey]`. Establish `k2 : c • c • c • (h * g) t = x (y (z v))`. Establish `e1 : c • (h * g) t = x (h (g v))`.

Rewrite using `[← map_smul, ← ex, Module.End.mul_apply]`. Express the relevant statement in the definitionally equal form `(h * (g * x)) v = x (h (g v))`. Rewrite using `[hgx, ← _root_.mul_assoc, hhx, _root_.mul_assoc]`. Both sides reduce to the same expression. Establish `e2 : c • x (h (g v)) = x (y (h v))`.

Rewrite using `[← map_smul, ← map_smul, ← ey]`. Express the relevant statement in the definitionally equal form `x ((h * y) v) = x ((y * h) v)`. Rewrite using `[hcen h hh y hy]`. Rewrite using `[e1, e2, ← map_smul, ← map_smul, ← ez]`. Establish `k3 : x (z (y v)) = x (y (z v))`.

Express the relevant statement in the definitionally equal form `(x * (z * y)) v = (x * (y * z)) v`. Rewrite using `[hcomm z hz y hy]`. Establish `k4 : (c * c * c) • (g * h) t = (c * c * c) • (h * g) t`. Rewrite using `[mul_smul, mul_smul, k1, k3, ← k2, mul_smul, mul_smul]`. Conclude with `smul_right_injective T (mul_ne_zero (mul_ne_zero hc hc) hc) k4`.
-/
theorem commute_of_cyclic {l : ℕ} [Fact l.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
    [Module.IsTorsionFree ℤ_[l] T] {O : Type} [CommRing O] (ρ : O →+* Module.End ℤ_[l] T) (v : T) (c : ℤ_[l])
    (hc : c ≠ 0) (hv : ∀ t : T, c • t ∈ Submodule.span ℤ_[l] (Set.range fun a => ρ a v))
    (g h : Module.End ℤ_[l] T) (hg : ∀ a, g * ρ a = ρ a * g) (hh : ∀ a, h * ρ a = ρ a * h) :
    g * h = h * g := by
  set P := Submodule.span ℤ_[l] (Set.range ρ) with hP
  have hcen : ∀ k : Module.End ℤ_[l] T, (∀ a, k * ρ a = ρ a * k) → ∀ x ∈ P, k * x = x * k := by
    intro k hk x hx
    have : P ≤ Subalgebra.toSubmodule (Subalgebra.centralizer ℤ_[l] {k}) := by
      rw [hP, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact hk a
    have h1 := this hx
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at h1
    exact h1 k rfl
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hx' : ∀ a, x * ρ a = ρ a * x := fun a => by
      have := hcen (ρ a) (fun b => by rw [← map_mul, ← map_mul, mul_comm]) x hx
      exact this.symm
    exact hcen x hx' y hy
  have hev : ∀ w : T, ∃ x ∈ P, x v = c • w := by
    intro w
    have := hv w
    rw [show (Set.range fun a => ρ a v) = (LinearMap.applyₗ v : Module.End ℤ_[l] T →ₗ[ℤ_[l]] T) '' Set.range ρ by
      rw [← Set.range_comp]; rfl, Submodule.span_image] at this
    obtain ⟨x, hx, e⟩ := this
    exact ⟨x, hx, e⟩
  refine LinearMap.ext fun t => ?_
  obtain ⟨x, hx, ex⟩ := hev t
  obtain ⟨y, hy, ey⟩ := hev (g v)
  obtain ⟨z, hz, ez⟩ := hev (h v)
  have hgx := hcen g hg x hx
  have hhx := hcen h hh x hx
  have k1 : c • c • c • (g * h) t = x (z (y v)) := by
    have e1 : c • (g * h) t = x (g (h v)) := by
      rw [← map_smul, ← ex, Module.End.mul_apply]
      change (g * (h * x)) v = x (g (h v))
      rw [hhx, ← _root_.mul_assoc, hgx, _root_.mul_assoc]; rfl
    have e2 : c • x (g (h v)) = x (z (g v)) := by
      rw [← map_smul, ← map_smul, ← ez]
      change x ((g * z) v) = x ((z * g) v)
      rw [hcen g hg z hz]
    rw [e1, e2, ← map_smul, ← map_smul, ← ey]
  have k2 : c • c • c • (h * g) t = x (y (z v)) := by
    have e1 : c • (h * g) t = x (h (g v)) := by
      rw [← map_smul, ← ex, Module.End.mul_apply]
      change (h * (g * x)) v = x (h (g v))
      rw [hgx, ← _root_.mul_assoc, hhx, _root_.mul_assoc]; rfl
    have e2 : c • x (h (g v)) = x (y (h v)) := by
      rw [← map_smul, ← map_smul, ← ey]
      change x ((h * y) v) = x ((y * h) v)
      rw [hcen h hh y hy]
    rw [e1, e2, ← map_smul, ← map_smul, ← ez]
  have k3 : x (z (y v)) = x (y (z v)) := by
    change (x * (z * y)) v = (x * (y * z)) v
    rw [hcomm z hz y hy]
  have k4 : (c * c * c) • (g * h) t = (c * c * c) • (h * g) t := by
    rw [mul_smul, mul_smul, k1, k3, ← k2, mul_smul, mul_smul]
  exact smul_right_injective T (mul_ne_zero (mul_ne_zero hc hc) hc) k4

/- English proof (translation)
The claim follows from `LinearMap.ext fun t => Tate.ext fun n => by change specAut σ ≫ (t.lev n ≫ α.act a) = (specAut σ ≫ t.lev n) ≫ α.act a rw [Category.assoc]`.
-/
theorem galTate_comm_actTate {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] {O : Type} [CommRing O] (α : OAct O A) (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[K] Ω) (a : O) :
    galTate A l σ * actTate α.toRingAct l (ptOver K Ω) a = actTate α.toRingAct l (ptOver K Ω) a * galTate A l σ :=
  LinearMap.ext fun t => Tate.ext fun n => by
    change specAut σ ≫ (t.lev n ≫ α.act a) = (specAut σ ≫ t.lev n) ≫ α.act a
    rw [Category.assoc]

/- English proof (translation)
Introduce `K Ω _ _ _ _ A _ _ hA F _ _ hF l _ hl σ τ`. Take `⟨⟨d, hd, hdeg⟩, O, _, _, _, ⟨α⟩⟩` from `hF`. Use `haveI : IsSepClosed Ω := IsSepClosure.sep_closed K`. Establish `hcard : ∀ n : ℕ, Nat.card {x : ptOver K Ω ⟶ A // x ^ (l ^ n) = 1} = l ^ (2 * d * n)` using `fun n => by`. Rewrite using `[GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K Ω A hA d hd (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), ← pow_mul, mul_comm n]`.

Take `⟨hfree, hfin, hrank⟩` from `GlobalTheory.TateFree.free_finite_finrank (ptOver K Ω ⟶ A) l (2 * d) hcard`. Use `haveI := hfree`. Use `haveI := hfin`. Take `⟨v, c, hc, hv⟩` from `GlobalTheory.T.exists_smul_mem_span_orbit_of_numberField_lattice l (Tate l (ptOver K Ω ⟶ A)) O F (actTate α.toRingAct l (ptOver K Ω)) (hrank.trans hdeg.symm) (GlobalTheory.T.linearIndependent_numberFieldEndomorphisms_tateModule K Ω A hA ⟨d, by have := Module.finrank_pos (R := ℚ) …`. Conclude with `commute_of_cyclic _ v c hc hv _ _ (galTate_comm_actTate A α l σ) (galTate_comm_actTate A α l τ)`.
-/
theorem galTate_commute_of_hasCMBy : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F], HasCMBy A F → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ := by
  intro K Ω _ _ _ _ A _ _ hA F _ _ hF l _ hl σ τ
  obtain ⟨⟨d, hd, hdeg⟩, O, _, _, _, ⟨α⟩⟩ := hF
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hcard : ∀ n : ℕ, Nat.card {x : ptOver K Ω ⟶ A // x ^ (l ^ n) = 1} = l ^ (2 * d * n) := fun n => by
    rw [GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K Ω A hA d hd (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), ← pow_mul, mul_comm n]
  obtain ⟨hfree, hfin, hrank⟩ := GlobalTheory.TateFree.free_finite_finrank (ptOver K Ω ⟶ A) l (2 * d) hcard
  haveI := hfree
  haveI := hfin
  obtain ⟨v, c, hc, hv⟩ := GlobalTheory.T.exists_smul_mem_span_orbit_of_numberField_lattice l (Tate l (ptOver K Ω ⟶ A)) O F (actTate α.toRingAct l (ptOver K Ω))
    (hrank.trans hdeg.symm) (GlobalTheory.T.linearIndependent_numberFieldEndomorphisms_tateModule K Ω A hA
      ⟨d, by have := Module.finrank_pos (R := ℚ) (M := F); omega, hd⟩ F O α l hl)
  exact commute_of_cyclic _ v c hc hv _ _ (galTate_comm_actTate A α l σ) (galTate_comm_actTate A α l τ)

end GlobalTheory.CMComm
