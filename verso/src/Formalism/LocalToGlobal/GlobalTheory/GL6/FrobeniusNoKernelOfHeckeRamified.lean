import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondPreservesForms
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondCommDistinctPlaces
import Formalism.LocalToGlobal.GlobalTheory.GL6.FrobeniusIdentitiesNoKernelOfClauses
import Formalism.LocalToGlobal.GlobalTheory.GL6.FrameTranslate
import Formalism.LocalToGlobal.GlobalTheory.GL6.EqOneOfCoprimeTorsionTwoPrimes

noncomputable section

open Classical Finset

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

section Gen

/- English proof (translation)
Rewrite using `[← Finset.sum_filter_add_sum_filter_not _ (fun g : Module.Dual k M => g te = 0)]`. Use `set S0 := (Finset.univ.filter (fun g : Module.Dual k M => g ≠ 0)).filter (fun g => g te = 0) with hS0`. Establish `hmem0 : ∀ g, g ∈ S0 ↔ g ≠ 0 ∧ g te = 0`. Introduce `g`. Simplify using `[hS0]`.

Establish `hZ0 : ∑ g ∈ S0, ψ (g te) • Tg g = 0`. Establish `e1 : ∑ g ∈ S0, ψ (g te) • Tg g = ∑ g ∈ S0, Tg g`. Use `Finset.sum_congr rfl (fun g hg => ?_)` and prove the remaining obligations. Rewrite using `[((hmem0 g).1 hg).2, AddChar.map_zero_eq_one, one_smul]`. Rewrite using `[e1]`.

Establish `e2 : ∀ a : kˣ, ∑ g ∈ S0, Tg ((a : k) • g) = ∑ g ∈ S0, Tg g`. Introduce `a`. Use `Finset.sum_nbij' (fun g => (a : k) • g) (fun g => ((a⁻¹ : kˣ) : k) • g) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `g hg`. Take `⟨h1, h2⟩` from `(hmem0 g).1 hg`.

Conclude with `(hmem0 _).2 ⟨smul_ne_zero (Units.ne_zero a) h1, by simp [h2]⟩`. Introduce `g hg`. Take `⟨h1, h2⟩` from `(hmem0 g).1 hg`. Conclude with `(hmem0 _).2 ⟨smul_ne_zero (Units.ne_zero _) h1, by simp [h2]⟩`. Introduce `g _`.

Simplify using `[smul_smul]`. Introduce `g _`. Simplify using `[smul_smul]`. Introduce `g _`. Both sides reduce to the same expression.

Establish `e3 : ∑ a : kˣ, ∑ g ∈ S0, Tg ((a : k) • g) = 0`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_eq_zero (fun g hg => hZ g ((hmem0 g).1 hg).1)`. Establish `e4 : ((Fintype.card kˣ : ℕ) : ℂ) • ∑ g ∈ S0, Tg g = 0`. Rewrite using `[Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.sum_const, ← e3]`.

Conclude with `Finset.sum_congr rfl (fun a _ => (e2 a).symm)`. Establish `hne : ((Fintype.card kˣ : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Use `congrArg (fun x => (((Fintype.card kˣ : ℕ) : ℂ))⁻¹ • x) e4` as an intermediate fact. Simplify `this` using `[smul_smul, inv_mul_cancel₀ hne]`. Rewrite using `[hZ0, zero_add]`.

Rewrite using `[← Finset.sum_product' (f := fun g (a : kˣ) => ψ (a : k) • Tg ((a : k) • g))]`. Use `symm`. Use `Finset.sum_bij' (fun p _ => (p.2 : k) • p.1) (fun g hg => ((g te)⁻¹ • g, Units.mk0 (g te) (Finset.mem_filter.1 hg).2)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Establish `h1 : p.1 te = 1` using `(Finset.mem_filter.1 (Finset.mem_product.1 hp).1).2`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.smul_apply, smul_eq_mul, h1, mul_one]`. Conclude with `⟨smul_ne_zero (Units.ne_zero _) (fun h0 => by rw [h0, LinearMap.zero_apply] at h1; exact zero_ne_one h1), Units.ne_zero _⟩`. Introduce `g hg`. Establish `h0 : g te ≠ 0` using `(Finset.mem_filter.1 hg).2`. Simplify using `only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true, LinearMap.smul_apply, smul_eq_mul]`.

Conclude with `inv_mul_cancel₀ h0`. Introduce `p hp`. Establish `h1 : p.1 te = 1` using `(Finset.mem_filter.1 (Finset.mem_product.1 hp).1).2`. Establish `e : ((p.2 : k) • p.1) te = p.2` using `by simp [h1]`. Use `ext1`.

Simplify using `only [e, smul_smul, inv_mul_cancel₀ (Units.ne_zero p.2), one_smul]`. Use `ext`. Simplify using `[e]`. Introduce `g hg`. Establish `h0 : g te ≠ 0` using `(Finset.mem_filter.1 hg).2`.

Simplify using `[smul_smul, mul_inv_cancel₀ h0]`. Introduce `p hp`. Establish `h1 : p.1 te = 1` using `(Finset.mem_filter.1 (Finset.mem_product.1 hp).1).2`. Simplify using `[h1]`.
-/
theorem character_sum_nonzero_duals {k M V : Type} [Field k] [Fintype k] [DecidableEq k] [AddCommGroup M] [Module k M] [Fintype (Module.Dual k M)]
    [AddCommGroup V] [Module ℂ V] (ψ : AddChar k ℂ) (te : M) (Tg : Module.Dual k M → V)
    (hZ : ∀ g : Module.Dual k M, g ≠ 0 → ∑ a : kˣ, Tg ((a : k) • g) = 0) :
    ∑ g ∈ Finset.univ.filter (fun g : Module.Dual k M => g ≠ 0), ψ (g te) • Tg g =
      ∑ g ∈ Finset.univ.filter (fun g : Module.Dual k M => g te = 1), ∑ a : kˣ, ψ (a : k) • Tg ((a : k) • g) := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun g : Module.Dual k M => g te = 0)]
  set S0 := (Finset.univ.filter (fun g : Module.Dual k M => g ≠ 0)).filter (fun g => g te = 0) with hS0
  have hmem0 : ∀ g, g ∈ S0 ↔ g ≠ 0 ∧ g te = 0 := by
    intro g; simp [hS0]
  have hZ0 : ∑ g ∈ S0, ψ (g te) • Tg g = 0 := by
    have e1 : ∑ g ∈ S0, ψ (g te) • Tg g = ∑ g ∈ S0, Tg g := by
      refine Finset.sum_congr rfl (fun g hg => ?_)
      rw [((hmem0 g).1 hg).2, AddChar.map_zero_eq_one, one_smul]
    rw [e1]
    have e2 : ∀ a : kˣ, ∑ g ∈ S0, Tg ((a : k) • g) = ∑ g ∈ S0, Tg g := by
      intro a
      refine Finset.sum_nbij' (fun g => (a : k) • g) (fun g => ((a⁻¹ : kˣ) : k) • g) ?_ ?_ ?_ ?_ ?_
      · intro g hg
        obtain ⟨h1, h2⟩ := (hmem0 g).1 hg
        exact (hmem0 _).2 ⟨smul_ne_zero (Units.ne_zero a) h1, by simp [h2]⟩
      · intro g hg
        obtain ⟨h1, h2⟩ := (hmem0 g).1 hg
        exact (hmem0 _).2 ⟨smul_ne_zero (Units.ne_zero _) h1, by simp [h2]⟩
      · intro g _; simp [smul_smul]
      · intro g _; simp [smul_smul]
      · intro g _; rfl
    have e3 : ∑ a : kˣ, ∑ g ∈ S0, Tg ((a : k) • g) = 0 := by
      rw [Finset.sum_comm]
      exact Finset.sum_eq_zero (fun g hg => hZ g ((hmem0 g).1 hg).1)
    have e4 : ((Fintype.card kˣ : ℕ) : ℂ) • ∑ g ∈ S0, Tg g = 0 := by
      rw [Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.sum_const, ← e3]
      exact Finset.sum_congr rfl (fun a _ => (e2 a).symm)
    have hne : ((Fintype.card kˣ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have := congrArg (fun x => (((Fintype.card kˣ : ℕ) : ℂ))⁻¹ • x) e4
    simpa [smul_smul, inv_mul_cancel₀ hne] using this
  rw [hZ0, zero_add]
  rw [← Finset.sum_product' (f := fun g (a : kˣ) => ψ (a : k) • Tg ((a : k) • g))]
  symm
  refine Finset.sum_bij' (fun p _ => (p.2 : k) • p.1)
    (fun g hg => ((g te)⁻¹ • g, Units.mk0 (g te) (Finset.mem_filter.1 hg).2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have h1 : p.1 te = 1 := (Finset.mem_filter.1 (Finset.mem_product.1 hp).1).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.smul_apply, smul_eq_mul, h1, mul_one]
    exact ⟨smul_ne_zero (Units.ne_zero _) (fun h0 => by rw [h0, LinearMap.zero_apply] at h1; exact zero_ne_one h1),
      Units.ne_zero _⟩
  · intro g hg
    have h0 : g te ≠ 0 := (Finset.mem_filter.1 hg).2
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true, LinearMap.smul_apply,
      smul_eq_mul]
    exact inv_mul_cancel₀ h0
  · intro p hp
    have h1 : p.1 te = 1 := (Finset.mem_filter.1 (Finset.mem_product.1 hp).1).2
    have e : ((p.2 : k) • p.1) te = p.2 := by simp [h1]
    ext1
    · simp only [e, smul_smul, inv_mul_cancel₀ (Units.ne_zero p.2), one_smul]
    · ext; simp [e]
  · intro g hg
    have h0 : g te ≠ 0 := (Finset.mem_filter.1 hg).2
    simp [smul_smul, mul_inv_cancel₀ h0]
  · intro p hp
    have h1 : p.1 te = 1 := (Finset.mem_filter.1 (Finset.mem_product.1 hp).1).2
    simp [h1]

end Gen

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 2000000 in

def DnDilLoc (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ),
    (k : (D.mem u).A.Fv v) = a → g ≠ 0 →
    ∀ δ, IsDia (Tf.cls i hi).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 k δ →
    ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
        (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
        ((Tf.cls i hi).y ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))).1 = ((Tf.cls i hi).y c).1 * η'.1 * κ'.1 →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) =
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
        (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = ((a : (D.mem u).A.Fv v) • g) ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    δ.1⁻¹ * η.1⁻¹ * η'.1 ∈ (Tf.cls i hi).lev.U

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨f, hf, hfφ⟩` from `forms_from_adelic_function Tf i hi φ hφ`. Establish `hfA` using `(Submodule.mem_inf.1 hf).1`. Take `⟨k, hk, δ, hδ⟩` from `diamond_elements_exist_all Tf i hi v a`. Establish `hb` using `level_places_not_bad Tf.atT v`. Establish `hF` using `adelic_function_right_translate_diamond (Tf.cls i hi).lev (embT D) (Tf.atT.eV v).1 (Tf.atT.eV v).2 hb hδ hfA`.

Establish `hag : (a : (D.mem u).A.Fv v) • g ≠ 0` using `smul_ne_zero (Units.ne_zero a) hg`. Take `⟨γ, η, κ, hsup, hrel, hl1, hfun, htr⟩` from `Tf.dn i hi v c g hg`. Take `⟨γ', η', κ', hsup', hrel', hl1', hfun', htr'⟩` from `Tf.dn i hi v c _ hag`. Establish `hk0` using `hL i hi v c g a k hk hg δ hδ γ η κ hsup hrel hl1 hfun γ' η' κ' hsup' hrel' hl1' hfun'`. Establish `e1 : Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ((D.fm u).dn i v c g) = fun z => f ((Tf.cls i hi).y ((D.fm u).dn i v c g) * δ) ((Tf.val i hi).eY z)` using `by show (D.fm u).dilT i v a ((D.fm u).dn i v c g) (φ ((D.fm u).dil i v a ((D.fm u).dn i v c g))) = _`.

Rewrite using `[hfφ]`. Conclude with `(Tf.val i hi).dilT v a k hk _ δ hδ f hfA`. Establish `h1` using `htr (fun x => f (x * δ)) hF`. Rewrite using `[e1, h1, hfφ, htr' f hfA]`. Use function extensionality and compare the values at `s`.

Establish `hx : ((Tf.cls i hi).y c * η').1 = bc (inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (1 : GL (Fin (D.R.N i)) D.host.E) * ((Tf.cls i hi).y c * η * δ).1 * (⟨_, hk0⟩ : (Tf.cls i hi).lev.U).1 := by`. Simplify using `only [Subgroup.coe_mul, map_one, one_mul]`. Use `group`. Establish `hval` using `adelic_value_translate (Tf.cls i hi).lev (embT D) (fun τ x => embedding_conj_compat D τ x) hfA 1 (UJ _ _).one_mem _ _ ⟨_, hk0⟩ hx ((Tf.val i hi).eY s)`. Establish `hχ : (Tf.cls i hi).lev.chi ⟨_, hk0⟩ = 1`.

Apply `(Tf.cls i hi).lev.chi_triv` to reduce the goal to its premises. Introduce `v'' hv''`. Establish `hne : v'' ≠ (Tf.atT.eV v).1` using `fun e => hb (e ▸ hv'')`. Simplify using `only [map_mul, map_inv, hδ.1 v'' hne, hsup v'' hne, hsup' v'' hne, inv_one, mul_one]`. Rewrite using `[hval, hχ, Units.val_one, one_mul, rnd_tr_congr (embT D) (fun τ x => embedding_conj_compat D τ x) inv_one _ (UJ _ _).one_mem, rnd_tr_one]`.
-/
theorem down_transport_diamond (Tf : FormsTied D u) (hL : DnDilLoc Tf) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (c : (D.mem u).C.cls i) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (hg : g ≠ 0)
    (a : ((D.mem u).A.Fv v)ˣ) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (hφ : φ ∈ (D.fm u).Fi i) :
    (D.fm u).dnT i v c g (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ((D.fm u).dn i v c g)) =
      (D.fm u).dnT i v c ((a : (D.mem u).A.Fv v) • g) (φ ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))) := by
  obtain ⟨f, hf, hfφ⟩ := forms_from_adelic_function Tf i hi φ hφ
  have hfA := (Submodule.mem_inf.1 hf).1
  obtain ⟨k, hk, δ, hδ⟩ := diamond_elements_exist_all Tf i hi v a
  have hb := level_places_not_bad Tf.atT v
  have hF := adelic_function_right_translate_diamond (Tf.cls i hi).lev (embT D) (Tf.atT.eV v).1 (Tf.atT.eV v).2 hb hδ hfA
  have hag : (a : (D.mem u).A.Fv v) • g ≠ 0 := smul_ne_zero (Units.ne_zero a) hg
  obtain ⟨γ, η, κ, hsup, hrel, hl1, hfun, htr⟩ := Tf.dn i hi v c g hg
  obtain ⟨γ', η', κ', hsup', hrel', hl1', hfun', htr'⟩ := Tf.dn i hi v c _ hag
  have hk0 := hL i hi v c g a k hk hg δ hδ γ η κ hsup hrel hl1 hfun γ' η' κ' hsup' hrel' hl1' hfun'
  have e1 : Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ((D.fm u).dn i v c g) =
      fun z => f ((Tf.cls i hi).y ((D.fm u).dn i v c g) * δ) ((Tf.val i hi).eY z) := by
    show (D.fm u).dilT i v a ((D.fm u).dn i v c g) (φ ((D.fm u).dil i v a ((D.fm u).dn i v c g))) = _
    rw [hfφ]
    exact (Tf.val i hi).dilT v a k hk _ δ hδ f hfA
  have h1 := htr (fun x => f (x * δ)) hF
  rw [e1, h1, hfφ, htr' f hfA]
  funext s
  have hx : ((Tf.cls i hi).y c * η').1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (1 : GL (Fin (D.R.N i)) D.host.E) *
        ((Tf.cls i hi).y c * η * δ).1 * (⟨_, hk0⟩ : (Tf.cls i hi).lev.U).1 := by
    simp only [Subgroup.coe_mul, map_one, one_mul]
    group
  have hval := adelic_value_translate (Tf.cls i hi).lev (embT D) (fun τ x => embedding_conj_compat D τ x) hfA 1
    (UJ _ _).one_mem _ _ ⟨_, hk0⟩ hx ((Tf.val i hi).eY s)
  have hχ : (Tf.cls i hi).lev.chi ⟨_, hk0⟩ = 1 := by
    apply (Tf.cls i hi).lev.chi_triv
    intro v'' hv''
    have hne : v'' ≠ (Tf.atT.eV v).1 := fun e => hb (e ▸ hv'')
    simp only [map_mul, map_inv, hδ.1 v'' hne, hsup v'' hne, hsup' v'' hne, inv_one, mul_one]
  rw [hval, hχ, Units.val_one, one_mul, rnd_tr_congr (embT D) (fun τ x => embedding_conj_compat D τ x) inv_one _ (UJ _ _).one_mem,
    rnd_tr_one]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Unfold `Formalism.MainNotions.product_first_zeroth_parts.FFop`. Rewrite using `[LinearMap.pi_apply, LinearMap.sum_apply]`. Both sides reduce to the same expression.
-/
theorem frobenius_eq_dual_sum (i : ℕ) (v : (D.mem u).A.vT) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (c : (D.mem u).C.cls i) :
    Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ c = ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) => g ≠ 0),
      (D.mem u).A.psiT v (g ((D.fm u).te i v c)) • (D.fm u).dnT i v c g (φ ((D.fm u).dn i v c g)) := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.FFop
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  rfl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Unfold `Formalism.MainNotions.product_first_zeroth_parts.Dop`. Rewrite using `[LinearMap.pi_apply, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl (fun g _ => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.proj_apply]`. Unfold `Formalism.MainNotions.product_first_zeroth_parts.Gs`.

Rewrite using `[LinearMap.sum_apply, Finset.sum_apply, map_sum]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, Pi.smul_apply, map_smul]`. Both sides reduce to the same expression.
-/
theorem frobenius_diamond_character_sum (i : ℕ) (v : (D.mem u).A.vT) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (c : (D.mem u).C.cls i) :
    Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ) c = ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) => g ((D.fm u).te i v c) = 1),
      ∑ a : ((D.mem u).A.Fv v)ˣ, (D.mem u).A.psiT v (a : (D.mem u).A.Fv v) •
        (D.fm u).dnT i v c g (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ((D.fm u).dn i v c g)) := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.Dop
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [LinearMap.comp_apply, LinearMap.proj_apply]
  unfold Formalism.MainNotions.product_first_zeroth_parts.Gs
  rw [LinearMap.sum_apply, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [LinearMap.smul_apply, Pi.smul_apply, map_smul]
  rfl

/- English proof (translation)
Unfold `Formalism.MainNotions.product_first_zeroth_parts.Nm`. Rewrite using `[LinearMap.sum_apply, Finset.sum_apply]`.
-/
theorem sum_diamond_eq_norm (i : ℕ) (v : (D.mem u).A.vT) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (c : (D.mem u).C.cls i) :
    ∑ a : ((D.mem u).A.Fv v)ˣ, Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ c = Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v φ c := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.Nm
  rw [LinearMap.sum_apply, Finset.sum_apply]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `i hi v φ hφ`. Establish `hφF : φ ∈ (D.fm u).Fi i` using `(Submodule.mem_inf.1 hφ).1`. Establish `hN : Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v φ = 0`. Establish `h2` using `(Submodule.mem_inf.1 hφ).2`. Rewrite `h2` using `[Submodule.mem_iInf]`.

Conclude with `LinearMap.mem_ker.1 (h2 v)`. Use function extensionality and compare the values at `c`. Rewrite using `[frobenius_eq_dual_sum, frobenius_diamond_character_sum]`. Establish `hk : ∀ g ∈ Finset.univ.filter (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) => g ((D.fm u).te i v c) = 1), ∑ a : ((D.mem u).A.Fv v)ˣ, (D.mem u).A.psiT v (a : (D.mem u).A.Fv v) • (D.fm u).dnT i v c g (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ( …`. Introduce `g hg`.

Establish `hg0 : g ≠ 0`. Introduce `h0`. Use `(Finset.mem_filter.1 hg).2` as an intermediate fact. Rewrite `this` using `[h0, LinearMap.zero_apply]`. Conclude with `zero_ne_one this`.

Conclude with `Finset.sum_congr rfl (fun a _ => by rw [down_transport_diamond Tf hL i hi v c g hg0 a φ hφF])`. Rewrite using `[Finset.sum_congr rfl hk]`. Establish `hZ : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c), g ≠ 0 → ∑ a : ((D.mem u).A.Fv v)ˣ, (D.fm u).dnT i v c ((a : (D.mem u).A.Fv v) • g) (φ ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))) = 0`. Introduce `g hg`. Establish `e : ∀ a : ((D.mem u).A.Fv v)ˣ, (D.fm u).dnT i v c ((a : (D.mem u).A.Fv v) • g) (φ ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))) = (D.fm u).dnT i v c g (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ((D.fm u).dn i v c g))` using `fun a => (down_transport_diamond Tf hL i hi v c g hg a φ hφF).symm`.

Rewrite using `[Finset.sum_congr rfl (fun a _ => e a), ← map_sum, sum_diamond_eq_norm, hN]`. Conclude with `map_zero _`. Use `character_sum_nonzero_duals ((D.mem u).A.psiT v) ((D.fm u).te i v c) (fun g => (D.fm u).dnT i v c g (φ ((D.fm u).dn i v c g))) hZ` and compare the differences between its conclusion and the goal.
-/
theorem frobenius_eq_D_gauss_of_dilation (Tf : FormsTied D u) (hL : DnDilLoc Tf) :
    ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ = Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ) := by
  intro i hi v φ hφ
  have hφF : φ ∈ (D.fm u).Fi i := (Submodule.mem_inf.1 hφ).1
  have hN : Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v φ = 0 := by
    have h2 := (Submodule.mem_inf.1 hφ).2
    rw [Submodule.mem_iInf] at h2
    exact LinearMap.mem_ker.1 (h2 v)
  funext c
  rw [frobenius_eq_dual_sum, frobenius_diamond_character_sum]
  have hk : ∀ g ∈ Finset.univ.filter
      (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) => g ((D.fm u).te i v c) = 1),
      ∑ a : ((D.mem u).A.Fv v)ˣ, (D.mem u).A.psiT v (a : (D.mem u).A.Fv v) •
        (D.fm u).dnT i v c g (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ((D.fm u).dn i v c g)) =
      ∑ a : ((D.mem u).A.Fv v)ˣ, (D.mem u).A.psiT v (a : (D.mem u).A.Fv v) •
        (D.fm u).dnT i v c ((a : (D.mem u).A.Fv v) • g) (φ ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))) := by
    intro g hg
    have hg0 : g ≠ 0 := by
      intro h0; have := (Finset.mem_filter.1 hg).2; rw [h0, LinearMap.zero_apply] at this; exact zero_ne_one this
    exact Finset.sum_congr rfl (fun a _ => by rw [down_transport_diamond Tf hL i hi v c g hg0 a φ hφF])
  rw [Finset.sum_congr rfl hk]
  have hZ : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c), g ≠ 0 →
      ∑ a : ((D.mem u).A.Fv v)ˣ,
        (D.fm u).dnT i v c ((a : (D.mem u).A.Fv v) • g) (φ ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))) = 0 := by
    intro g hg
    have e : ∀ a : ((D.mem u).A.Fv v)ˣ,
        (D.fm u).dnT i v c ((a : (D.mem u).A.Fv v) • g) (φ ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))) =
          (D.fm u).dnT i v c g (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ((D.fm u).dn i v c g)) :=
      fun a => (down_transport_diamond Tf hL i hi v c g hg a φ hφF).symm
    rw [Finset.sum_congr rfl (fun a _ => e a), ← map_sum, sum_diamond_eq_norm, hN]
    exact map_zero _
  convert character_sum_nonzero_duals ((D.mem u).A.psiT v) ((D.fm u).te i v c)
    (fun g => (D.fm u).dnT i v c g (φ ((D.fm u).dn i v c g))) hZ

section Rest

variable {D : D7} {u : D.what₂.Word}

/- English proof (translation)
Establish `hE` using `diamond_elements_exist_all Tf`. Establish `hφF : φ ∈ (D.fm u).Fi i` using `(Submodule.mem_inf.1 hφ).1`. Establish `hN : ∀ v', Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v' φ = 0`. Introduce `v'`. Establish `h2` using `(Submodule.mem_inf.1 hφ).2`.

Rewrite `h2` using `[Submodule.mem_iInf]`. Conclude with `LinearMap.mem_ker.1 (h2 v')`. Use `Submodule.mem_inf.2 ⟨?_, (Submodule.mem_iInf _).2 (fun v' => LinearMap.mem_ker.2 ?_)⟩` and prove the remaining obligations. Unfold `Formalism.MainNotions.product_first_zeroth_parts.Gs`. Rewrite using `[LinearMap.sum_apply]`.

Conclude with `Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (diamond_preserves_forms Tf hE i hi v a φ hφF))`. Establish `hc : ∀ (a : ((D.mem u).A.Fv v)ˣ) (b : ((D.mem u).A.Fv v')ˣ), Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' b (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ) = Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a (Formalism.MainNotions. …`. Introduce `a b`. Distinguish the cases in `hvv : v = v'`. Substitute `hvv` using the available equality.

Conclude with `diamond_comm_same_place Tf hE i hi v b a φ hφF`. Conclude with `diamond_comm_distinct_places Tf hE i hi v v' hvv b a φ hφF`. Establish `e : Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v' (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ) = Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v (Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v' φ)`. Unfold `Formalism.MainNotions.product_first_zeroth_parts.Nm Formalism.MainNotions.product_first_zeroth_parts.Gs`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hc b a]))`. Rewrite using `[e, hN v', map_zero]`.
-/
theorem gauss_sum_preserves_ramified (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i)
    (hφ : φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i) : Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i := by
  have hE := diamond_elements_exist_all Tf
  have hφF : φ ∈ (D.fm u).Fi i := (Submodule.mem_inf.1 hφ).1
  have hN : ∀ v', Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v' φ = 0 := by
    intro v'
    have h2 := (Submodule.mem_inf.1 hφ).2
    rw [Submodule.mem_iInf] at h2
    exact LinearMap.mem_ker.1 (h2 v')
  refine Submodule.mem_inf.2 ⟨?_, (Submodule.mem_iInf _).2 (fun v' => LinearMap.mem_ker.2 ?_)⟩
  · unfold Formalism.MainNotions.product_first_zeroth_parts.Gs
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (diamond_preserves_forms Tf hE i hi v a φ hφF))
  · have hc : ∀ (a : ((D.mem u).A.Fv v)ˣ) (b : ((D.mem u).A.Fv v')ˣ),
        Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' b (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ) =
          Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' b φ) := by
      intro a b
      by_cases hvv : v = v'
      · subst hvv
        exact diamond_comm_same_place Tf hE i hi v b a φ hφF
      · exact diamond_comm_distinct_places Tf hE i hi v v' hvv b a φ hφF
    have e : Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v' (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ) =
        Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v (Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v' φ) := by
      unfold Formalism.MainNotions.product_first_zeroth_parts.Nm Formalism.MainNotions.product_first_zeroth_parts.Gs
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hc b a]))
    rw [e, hN v', map_zero]

/- English proof (translation)
Introduce `i hi v φ hφ`. Rewrite using `[frobenius_eq_D_gauss_of_dilation Tf hL i hi v φ hφ]`. Conclude with `hD i hi v _ (gauss_sum_preserves_ramified Tf i hi v φ hφ)`.
-/
theorem FFop_mem_MramI_of_le_m (Tf : FormsTied D u) (hL : DnDilLoc Tf)
    (hD : ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i) :
    ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i := by
  intro i hi v φ hφ
  rw [frobenius_eq_D_gauss_of_dilation Tf hL i hi v φ hφ]
  exact hD i hi v _ (gauss_sum_preserves_ramified Tf i hi v φ hφ)

/- English proof (translation)
Unfold `Formalism.BasicNotions.MemberForms.ipC`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem class_form_smul_left (i : ℕ) (c : ℂ) (x y : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) :
    (D.fm u).ipC i (c • x) y = starRingEnd ℂ c * (D.fm u).ipC i x y := by
  unfold Formalism.BasicNotions.MemberForms.ipC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Pi.smul_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `Formalism.BasicNotions.MemberForms.ipC`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem class_form_smul_right (i : ℕ) (c : ℂ) (x y : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) :
    (D.fm u).ipC i x (c • y) = c * (D.fm u).ipC i x y := by
  unfold Formalism.BasicNotions.MemberForms.ipC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Pi.smul_apply, map_smul, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `Formalism.BasicNotions.MemberForms.ipC`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_apply, map_sum, LinearMap.sum_apply, Finset.mul_sum]`.
-/
theorem class_form_sum_left {ι : Type} (s : Finset ι) (i : ℕ) (x : ι → Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (y : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) :
    (D.fm u).ipC i (∑ a ∈ s, x a) y = ∑ a ∈ s, (D.fm u).ipC i (x a) y := by
  unfold Formalism.BasicNotions.MemberForms.ipC
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_apply, map_sum, LinearMap.sum_apply, Finset.mul_sum]

/- English proof (translation)
Unfold `Formalism.BasicNotions.MemberForms.ipC`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_apply, map_sum, Finset.mul_sum]`.
-/
theorem class_form_sum_right {ι : Type} (s : Finset ι) (i : ℕ) (x : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (y : ι → Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) :
    (D.fm u).ipC i x (∑ a ∈ s, y a) = ∑ a ∈ s, (D.fm u).ipC i x (y a) := by
  unfold Formalism.BasicNotions.MemberForms.ipC
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_apply, map_sum, Finset.mul_sum]

/- English proof (translation)
Establish `hE` using `diamond_elements_exist_all Tf`. Unfold `Formalism.MainNotions.product_first_zeroth_parts.Gs Formalism.MainNotions.product_first_zeroth_parts.GsD`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))` and prove the remaining obligations.

Rewrite using `[diamond_comm_same_place Tf hE i hi v x⁻¹ y φ hφ, mul_comm]`.
-/
theorem gauss_sum_commute_dual (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i)
    (hφ : φ ∈ (D.fm u).Fi i) :
    Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ) = Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v (Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v φ) := by
  have hE := diamond_elements_exist_all Tf
  unfold Formalism.MainNotions.product_first_zeroth_parts.Gs Formalism.MainNotions.product_first_zeroth_parts.GsD
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [diamond_comm_same_place Tf hE i hi v x⁻¹ y φ hφ, mul_comm]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `φ hφ ψ hψ`. Establish `hφF : φ ∈ (D.fm u).Fi i` using `(Submodule.mem_inf.1 hφ).1`. Establish `hψF : ψ ∈ (D.fm u).Fi i` using `(Submodule.mem_inf.1 hψ).1`. Establish `hGφ` using `gauss_sum_preserves_ramified Tf i hi v φ hφ`. Establish `hGψ` using `gauss_sum_preserves_ramified Tf i hi v ψ hψ`.

Establish `hNψ : Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v ψ = 0`. Establish `h2` using `(Submodule.mem_inf.1 hψ).2`. Rewrite `h2` using `[Submodule.mem_iInf]`. Conclude with `LinearMap.mem_ker.1 (h2 v)`. Rewrite using `[frobenius_eq_D_gauss_of_dilation Tf hL i hi v φ hφ, frobenius_eq_D_gauss_of_dilation Tf hL i hi v ψ hψ, ← h1c _ (Submodule.mem_inf.1 (hDm _ hGφ)).1 _ (Submodule.mem_inf.1 hGψ).1, hUD _ hGφ, class_form_smul_left]`.

Establish `hadj : (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ) (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v ψ) = (D.fm u).ipC i φ (Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v (Formalism.MainNotions.product_first_zeroth_parts …`. Establish `hGψF` using `(Submodule.mem_inf.1 hGψ).1`. Use `conv_lhs => rw [show Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ = ∑ a : ((D.mem u).A.Fv v)ˣ, (D.mem u).A.psiT v (a : (D.mem u).A.Fv v) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ by`. Unfold `Formalism.MainNotions.product_first_zeroth_parts.Gs`. Rewrite using `[LinearMap.sum_apply]`.

Use the proof step `rfl]`. Rewrite using `[class_form_sum_left]`. Unfold `Formalism.MainNotions.product_first_zeroth_parts.GsD`. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply]`.

Rewrite using `[class_form_sum_right]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[class_form_smul_left, class_form_smul_right, hAdj a φ hφF _ hGψF, ← AddChar.map_neg_eq_conj]`. Rewrite using `[hadj, gauss_sum_commute_dual Tf i hi v ψ hψF, gs_gsD_of_diaMul D u (DiaMul_tied Tf) i hi v ψ hψF, hNψ, sub_zero, class_form_smul_right]`. Establish `hN2` using `two_le_rank_of_level D i`.

Establish `e : D.R.N i = (D.R.N i - 1) + 1` using `by omega`. Use `conv_rhs => rw [e]`. Simplify using `only [map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frobenius_class_form_similitude_of_hecke (Tf : FormsTied D u) (hL : DnDilLoc Tf) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (h1c : ∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i,
      (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.Uop D u i v φ) ψ = (D.fm u).ipC i φ (Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v ψ))
    (hUD : ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      Formalism.MainNotions.product_first_zeroth_parts.Uop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ)
    (hDm : ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i)
    (hAdj : ∀ (a : ((D.mem u).A.Fv v)ˣ), ∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i,
      (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ) ψ = (D.fm u).ipC i φ (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ)) :
    ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, ∀ ψ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ) (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v ψ) =
        ((D.mem u).A.T : ℂ) ^ D.R.N i * (D.fm u).ipC i φ ψ := by
  intro φ hφ ψ hψ
  have hφF : φ ∈ (D.fm u).Fi i := (Submodule.mem_inf.1 hφ).1
  have hψF : ψ ∈ (D.fm u).Fi i := (Submodule.mem_inf.1 hψ).1
  have hGφ := gauss_sum_preserves_ramified Tf i hi v φ hφ
  have hGψ := gauss_sum_preserves_ramified Tf i hi v ψ hψ
  have hNψ : Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v ψ = 0 := by
    have h2 := (Submodule.mem_inf.1 hψ).2
    rw [Submodule.mem_iInf] at h2
    exact LinearMap.mem_ker.1 (h2 v)
  rw [frobenius_eq_D_gauss_of_dilation Tf hL i hi v φ hφ, frobenius_eq_D_gauss_of_dilation Tf hL i hi v ψ hψ,
    ← h1c _ (Submodule.mem_inf.1 (hDm _ hGφ)).1 _ (Submodule.mem_inf.1 hGψ).1, hUD _ hGφ, class_form_smul_left]
  have hadj : (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ) (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v ψ) =
      (D.fm u).ipC i φ (Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v ψ)) := by
    have hGψF := (Submodule.mem_inf.1 hGψ).1
    conv_lhs => rw [show Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ = ∑ a : ((D.mem u).A.Fv v)ˣ,
      (D.mem u).A.psiT v (a : (D.mem u).A.Fv v) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ by
        unfold Formalism.MainNotions.product_first_zeroth_parts.Gs; rw [LinearMap.sum_apply]; rfl]
    rw [class_form_sum_left]
    unfold Formalism.MainNotions.product_first_zeroth_parts.GsD
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [class_form_sum_right]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [class_form_smul_left, class_form_smul_right, hAdj a φ hφF _ hGψF, ← AddChar.map_neg_eq_conj]
  rw [hadj, gauss_sum_commute_dual Tf i hi v ψ hψF, gs_gsD_of_diaMul D u (DiaMul_tied Tf) i hi v ψ hψF, hNψ, sub_zero,
    class_form_smul_right]
  have hN2 := two_le_rank_of_level D i
  have e : D.R.N i = (D.R.N i - 1) + 1 := by omega
  conv_rhs => rw [e]
  simp only [map_pow, map_natCast]
  ring

/- English proof (translation)
Introduce `D u hF hS`. Take `⟨Tf, hc⟩` from `hF`. Take `⟨hL, hT⟩` from `h D u Tf hc hS`. Conclude with `frobenius_identities_no_kernel_of_clauses D u (frobenius_eq_D_gauss_of_dilation Tf hL) (FFop_mem_MramI_of_le_m Tf hL (fun i hi v => (hT i hi v).1)) (fun i hi v => frobenius_class_form_similitude_of_hecke Tf hL i hi v (hT i hi v).2.2.1 (hT i hi v).2.1 (hT i hi v).1 (hT i hi v).2.2 …`.
-/
theorem frobenius_no_kernel_of_hecke_ramified
    (h : ∀ (D : D7) (u : D.what₂.Word) (Tf : FormsTied D u), ChiFin Tf → Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u →
      DnDilLoc Tf ∧ ∀ i, i ≤ D.R.m → ∀ v,
        (∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i) ∧
        (∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
          Formalism.MainNotions.product_first_zeroth_parts.Uop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ) ∧
        (∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i,
          (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.Uop D u i v φ) ψ = (D.fm u).ipC i φ (Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v ψ)) ∧
        (∀ (a : ((D.mem u).A.Fv v)ˣ), ∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i,
          (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ) ψ = (D.fm u).ipC i φ (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ))) :
    FrobeniusNoKernelFamily := by
  intro D u hF hS
  obtain ⟨Tf, hc⟩ := hF
  obtain ⟨hL, hT⟩ := h D u Tf hc hS
  exact frobenius_identities_no_kernel_of_clauses D u (frobenius_eq_D_gauss_of_dilation Tf hL) (FFop_mem_MramI_of_le_m Tf hL (fun i hi v => (hT i hi v).1))
    (fun i hi v => frobenius_class_form_similitude_of_hecke Tf hL i hi v (hT i hi v).2.2.1 (hT i hi v).2.1 (hT i hi v).1 (hT i hi v).2.2.2)
    (DiaMul_tied Tf)

end Rest

section Adj

variable {D : D7} {u : D.what₂.Word}

/- English proof (translation)
Establish `h` using `(Tf.val i hi).dil v 1 1 (by simp) c 1 (is_diamond_one _ _ _)`. Rewrite `h` using `[mul_one]`. Conclude with `(Tf.cls i hi).y_bij.1 h`.
-/
theorem dilation_one (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    (D.fm u).dil i v 1 c = c := by
  have h := (Tf.val i hi).dil v 1 1 (by simp) c 1 (is_diamond_one _ _ _)
  rw [mul_one] at h
  exact (Tf.cls i hi).y_bij.1 h

/- English proof (translation)
Take `⟨ka, hka, δa, ha⟩` from `diamond_elements_exist_all Tf i hi v a`. Take `⟨kb, hkb, δb, hb⟩` from `diamond_elements_exist_all Tf i hi v b`. Establish `W` using `Tf.val i hi`. Establish `h1` using `W.dil v a ka hka ((D.fm u).dil i v b c) δa ha`. Establish `h2` using `W.dil v b kb hkb c δb hb`.

Establish `h3` using `class_mul_right_of_normalises _ _ _ _ δa (fun κ hκ => diamond_conj_mem_level' _ _ _ ha ⟨κ, hκ⟩) h2`. Establish `hab : ((kb * ka : ℤ) : (D.mem u).A.Fv v) = ((b * a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v)`. Rewrite using `[Int.cast_mul, hka, hkb, Units.val_mul]`. Establish `h4` using `W.dil v (b * a) (kb * ka) hab c (δb * δa) (is_diamond_mul_mult _ _ _ hb ha)`. Establish `h5 : (Quotient.mk'' ((Tf.cls i hi).y c * δb * δa) : Cls (Tf.cls i hi).lev) = Quotient.mk'' ((Tf.cls i hi).y c * (δb * δa))` using `by rw [mul_assoc]`.

Conclude with `(Tf.cls i hi).y_bij.1 (h1.trans (h3.trans (h5.trans h4.symm)))`.
-/
theorem dilation_mul (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (a b : ((D.mem u).A.Fv v)ˣ)
    (c : (D.mem u).C.cls i) :
    (D.fm u).dil i v a ((D.fm u).dil i v b c) = (D.fm u).dil i v (b * a) c := by
  obtain ⟨ka, hka, δa, ha⟩ := diamond_elements_exist_all Tf i hi v a
  obtain ⟨kb, hkb, δb, hb⟩ := diamond_elements_exist_all Tf i hi v b
  have W := Tf.val i hi
  have h1 := W.dil v a ka hka ((D.fm u).dil i v b c) δa ha
  have h2 := W.dil v b kb hkb c δb hb
  have h3 := class_mul_right_of_normalises _ _ _ _ δa (fun κ hκ => diamond_conj_mem_level' _ _ _ ha ⟨κ, hκ⟩) h2
  have hab : ((kb * ka : ℤ) : (D.mem u).A.Fv v) = ((b * a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) := by
    rw [Int.cast_mul, hka, hkb, Units.val_mul]
  have h4 := W.dil v (b * a) (kb * ka) hab c (δb * δa) (is_diamond_mul_mult _ _ _ hb ha)
  have h5 : (Quotient.mk'' ((Tf.cls i hi).y c * δb * δa) : Cls (Tf.cls i hi).lev) =
      Quotient.mk'' ((Tf.cls i hi).y c * (δb * δa)) := by rw [mul_assoc]
  exact (Tf.cls i hi).y_bij.1 (h1.trans (h3.trans (h5.trans h4.symm)))

/- English proof (translation)
Use `Function.bijective_iff_has_inverse.2 ⟨(D.fm u).dil i v a⁻¹, fun c => ?_, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[dilation_mul Tf i hi v a⁻¹ a c, mul_inv_cancel, dilation_one Tf i hi v c]`. Rewrite using `[dilation_mul Tf i hi v a a⁻¹ c, inv_mul_cancel, dilation_one Tf i hi v c]`.
-/
theorem dilation_bijective (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) :
    Function.Bijective ((D.fm u).dil i v a) := by
  refine Function.bijective_iff_has_inverse.2 ⟨(D.fm u).dil i v a⁻¹, fun c => ?_, fun c => ?_⟩
  · rw [dilation_mul Tf i hi v a⁻¹ a c, mul_inv_cancel, dilation_one Tf i hi v c]
  · rw [dilation_mul Tf i hi v a a⁻¹ c, inv_mul_cancel, dilation_one Tf i hi v c]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Establish `hE` using `diamond_elements_exist_all Tf`. Establish `hM` using `DiaMul_tied Tf`. Establish `hψ'` using `diamond_preserves_forms Tf hE i hi v a⁻¹ ψ hψ`. Establish `hψeq : ψ = Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ)`. Rewrite using `[← (hM i hi v ψ hψ).2 a a⁻¹, mul_inv_cancel, (hM i hi v ψ hψ).1]`.

Establish `hT` using `TrIso_tied Tf`. Use `conv_lhs => rw [hψeq]`. Unfold `Formalism.BasicNotions.MemberForms.ipC`. Establish `e1 : ∀ c, (D.mem u).C.wt i c * (D.fm u).ipV i c (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ c) (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ) c) = (fun c => (D.mem u).C.wt …`. Introduce `c`.

Establish `h` using `(hT i hi v c φ hφ _ hψ').2.2 a`. Use `show (D.mem u).C.wt i c * (D.fm u).ipV i c ((D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c))) ((D.fm u).dilT i v a c (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ ((D.fm u).dil i v a c))) = _`. Rewrite using `[h]`. Simplify using `only [Formalism.BasicNotions.ColumnChain.wt, (D.fm u).dil_stab]`. Rewrite using `[Finset.sum_congr rfl (fun c _ => e1 c)]`.

Conclude with `Equiv.sum_comp (Equiv.ofBijective _ (dilation_bijective Tf i hi v a)) (fun c => (D.mem u).C.wt i c * (D.fm u).ipV i c (φ c) (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ c))`.
-/
theorem diamond_adjoint_class_form (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ)
    (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (hφ : φ ∈ (D.fm u).Fi i) (ψ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (hψ : ψ ∈ (D.fm u).Fi i) :
    (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ) ψ = (D.fm u).ipC i φ (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ) := by
  have hE := diamond_elements_exist_all Tf
  have hM := DiaMul_tied Tf
  have hψ' := diamond_preserves_forms Tf hE i hi v a⁻¹ ψ hψ
  have hψeq : ψ = Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ) := by
    rw [← (hM i hi v ψ hψ).2 a a⁻¹, mul_inv_cancel, (hM i hi v ψ hψ).1]
  have hT := TrIso_tied Tf
  conv_lhs => rw [hψeq]
  unfold Formalism.BasicNotions.MemberForms.ipC
  have e1 : ∀ c, (D.mem u).C.wt i c * (D.fm u).ipV i c (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ c)
      (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ) c) =
      (fun c => (D.mem u).C.wt i c * (D.fm u).ipV i c (φ c) (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ c))
        ((D.fm u).dil i v a c) := by
    intro c
    have h := (hT i hi v c φ hφ _ hψ').2.2 a
    show (D.mem u).C.wt i c * (D.fm u).ipV i c ((D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c)))
      ((D.fm u).dilT i v a c (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ ((D.fm u).dil i v a c))) = _
    rw [h]
    simp only [Formalism.BasicNotions.ColumnChain.wt, (D.fm u).dil_stab]
  rw [Finset.sum_congr rfl (fun c _ => e1 c)]
  exact Equiv.sum_comp (Equiv.ofBijective _ (dilation_bijective Tf i hi v a))
    (fun c => (D.mem u).C.wt i c * (D.fm u).ipV i c (φ c) (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ c))

/- English proof (translation)
Apply `frobenius_no_kernel_of_hecke_ramified` to reduce the goal to its premises. Introduce `D u Tf hc hS`. Take `⟨hL, hT⟩` from `h D u Tf hc hS`. Conclude with `⟨hL, fun i hi v => ⟨(hT i hi v).1, (hT i hi v).2.1, (hT i hi v).2.2, fun a φ hφ ψ hψ => diamond_adjoint_class_form Tf i hi v a φ hφ ψ hψ⟩⟩`.
-/
theorem frobenius_no_kernel_of_hecke_ramified'
    (h : ∀ (D : D7) (u : D.what₂.Word) (Tf : FormsTied D u), ChiFin Tf → Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u →
      DnDilLoc Tf ∧ ∀ i, i ≤ D.R.m → ∀ v,
        (∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i) ∧
        (∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
          Formalism.MainNotions.product_first_zeroth_parts.Uop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ) ∧
        (∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i,
          (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.Uop D u i v φ) ψ = (D.fm u).ipC i φ (Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v ψ))) :
    FrobeniusNoKernelFamily := by
  apply frobenius_no_kernel_of_hecke_ramified
  intro D u Tf hc hS
  obtain ⟨hL, hT⟩ := h D u Tf hc hS
  exact ⟨hL, fun i hi v => ⟨(hT i hi v).1, (hT i hi v).2.1, (hT i hi v).2.2,
    fun a φ hφ ψ hψ => diamond_adjoint_class_form Tf i hi v a φ hφ ψ hψ⟩⟩

end Adj

/- English proof (translation)
Apply `frobenius_no_kernel_of_hecke_ramified'` to reduce the goal to its premises. Introduce `D u Tf hc hS`. Take `⟨_, _, c3, _, _, _, _, _, c9⟩` from `h1 D u ⟨Tf, hc⟩ hS`. Conclude with `⟨hL D u Tf hc, fun i hi v => ⟨fun φ hφ => (c9 i hi v φ hφ).2.1, fun φ hφ => (c9 i hi v φ hφ).2.2.2.2.2, c3 i hi v⟩⟩`.
-/
theorem frobenius_no_kernel_of_hecke_relations (h1 : HeckeRelationsFamily) (hL : ∀ (D : D7) (u : D.what₂.Word) (Tf : FormsTied D u), ChiFin Tf → DnDilLoc Tf) :
    FrobeniusNoKernelFamily := by
  apply frobenius_no_kernel_of_hecke_ramified'
  intro D u Tf hc hS
  obtain ⟨_, _, c3, _, _, _, _, _, c9⟩ := h1 D u ⟨Tf, hc⟩ hS
  exact ⟨hL D u Tf hc, fun i hi v => ⟨fun φ hφ => (c9 i hi v φ hφ).2.1, fun φ hφ => (c9 i hi v φ hφ).2.2.2.2.2,
    c3 i hi v⟩⟩

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
