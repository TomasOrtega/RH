import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityFixedDvdWeilGroupDegreeStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi.JEx

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w)

/- English proof (translation)
The claim follows from `ord_eq_zero_iff.1 (by rw [ha.ord_eq, deg_ineIncl, neg_zero])`.
-/
theorem art_ine {a : Weil h →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (σ : Ine (F := F) A) :
    a (ineIncl h σ) ∈ Uo (w.adicCompletion F) :=
  ord_eq_zero_iff.1 (by rw [ha.ord_eq, deg_ineIncl, neg_zero])

/- English proof (translation)
Establish `hd : DenseRange (Subgroup.inclusion (Weil_le_Dec h))` using `UpperTheory.weil_group_dense_in_galois_group F Ω w A h`. Establish `hdeg : deg s⁻¹ = 1`. Rewrite using `[deg_inv, ← ha.ord_eq, hs]`. Conclude with `ord_eq_one GlAx.unif_spec`. Use `letI : TopologicalSpace B := ⊥`.

Use `haveI : DiscreteTopology B := ⟨rfl⟩`. Use `hd.equalizer hχ.continuous (continuous_const (y := (1 : B))) (funext fun t => by` as an intermediate fact. Take `⟨τ, hτ⟩` from `exists_eq_zpow_mul hdeg t`. Express the relevant statement in the definitionally equal form `χ (Subgroup.inclusion (Weil_le_Dec h) t) = 1`. Rewrite using `[hτ, map_mul, map_mul, map_zpow, map_zpow, map_inv, map_inv, h1, inv_one, one_zpow, one_mul]`.

Conclude with `hI _ τ.2)`. Conclude with `MonoidHom.ext fun g => congrFun this g`.
-/
theorem char_triv {a : Weil h →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) {B : Type} [Group B]
    (χ : Dec (F := F) A →* B) (hχ : IsLocallyConstant χ) (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 1)
    (s : Weil h) (hs : a s = unif _) (h1 : χ (Subgroup.inclusion (Weil_le_Dec h) s) = 1) : χ = 1 := by
  have hd : DenseRange (Subgroup.inclusion (Weil_le_Dec h)) := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  have hdeg : deg s⁻¹ = 1 := by
    rw [deg_inv, ← ha.ord_eq, hs]
    exact ord_eq_one GlAx.unif_spec
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  have := hd.equalizer hχ.continuous (continuous_const (y := (1 : B))) (funext fun t => by
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul hdeg t
    change χ (Subgroup.inclusion (Weil_le_Dec h) t) = 1
    rw [hτ, map_mul, map_mul, map_zpow, map_zpow, map_inv, map_inv, h1, inv_one, one_zpow, one_mul]
    exact hI _ τ.2)
  exact MonoidHom.ext fun g => congrFun this g

/- English proof (translation)
Establish `hex : ∀ d : D, ∃ s : W, d⁻¹ * i s ∈ V`. Introduce `d`. Establish `ho : IsOpen {x : D | d⁻¹ * x ∈ V}` using `hV.preimage (continuous_const.mul continuous_id)`. Establish `hn : ({x : D | d⁻¹ * x ∈ V} : Set D).Nonempty` using `⟨d, by simp [V.one_mem]⟩`. Conclude with `hi.exists_mem_open ho hn`.

Establish `key : ∀ (d : D) (s s' : W), d⁻¹ * i s ∈ V → d⁻¹ * i s' ∈ V → χ s = χ s'`. Introduce `d s s' h1 h2`. Establish `h3 : i (s⁻¹ * s') ∈ V`. Establish `: i (s⁻¹ * s') = (d⁻¹ * i s)⁻¹ * (d⁻¹ * i s')`. Rewrite using `[map_mul, map_inv]`.

Use `group`. Rewrite using `[this]`. Conclude with `V.mul_mem (V.inv_mem h1) h2`. Establish `h4` using `hχ _ h3`. Rewrite `h4` using `[map_mul, map_inv, inv_mul_eq_one]`.

Conclude with `h4`. Use `choose f hf using hex`. Use `⟨{ toFun := fun d => χ (f d), map_one' := ?_, map_mul' := ?_ }, ?_, ?_⟩` and prove the remaining obligations. Use `show χ (f 1) = 1`. Rewrite using `[← χ.map_one]`.

Conclude with `key 1 _ _ (hf 1) (by simp [V.one_mem])`. Introduce `d1 d2 show χ (f (d1 * d2)) = χ (f d1) * χ (f d2)`. Rewrite using `[← map_mul]`. Apply `key (d1 * d2) _ _ (hf _)` to reduce the goal to its premises. Establish `e : (d1 * d2)⁻¹ * i (f d1 * f d2) = (d2⁻¹ * (d1⁻¹ * i (f d1)) * d2⁻¹⁻¹) * (d2⁻¹ * i (f d2))`.

Rewrite using `[map_mul]`. Use `group`. Rewrite using `[e]`. Conclude with `V.mul_mem (‹V.Normal›.conj_mem _ (hf d1) _) (hf d2)`. Rewrite using `[IsLocallyConstant.iff_exists_open]`.

Introduce `x`. Use `⟨{y : D | x⁻¹ * y ∈ V}, hV.preimage (continuous_const.mul continuous_id), by simp [V.one_mem], ?_⟩` and prove the remaining obligations. Introduce `y hy`. Use `show χ (f y) = χ (f x)`. Use `symm`.

Apply `key x _ _ (hf x)` to reduce the goal to its premises. Establish `e : x⁻¹ * i (f y) = (x⁻¹ * y) * (y⁻¹ * i (f y))` using `by group`. Rewrite using `[e]`. Conclude with `V.mul_mem hy (hf y)`. Introduce `s show χ (f (i s)) = χ s`.

Conclude with `key (i s) _ _ (hf _) (by simp [V.one_mem])`.
-/
private theorem ext_lc {D W B : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group W] [Group B]
    (i : W →* D) (hi : DenseRange i) (χ : W →* B) (V : Subgroup D) [V.Normal] (hV : IsOpen (V : Set D))
    (hχ : ∀ s, i s ∈ V → χ s = 1) : ∃ ψ : D →* B, IsLocallyConstant ψ ∧ ∀ s, ψ (i s) = χ s := by
  have hex : ∀ d : D, ∃ s : W, d⁻¹ * i s ∈ V := by
    intro d
    have ho : IsOpen {x : D | d⁻¹ * x ∈ V} := hV.preimage (continuous_const.mul continuous_id)
    have hn : ({x : D | d⁻¹ * x ∈ V} : Set D).Nonempty := ⟨d, by simp [V.one_mem]⟩
    exact hi.exists_mem_open ho hn
  have key : ∀ (d : D) (s s' : W), d⁻¹ * i s ∈ V → d⁻¹ * i s' ∈ V → χ s = χ s' := by
    intro d s s' h1 h2
    have h3 : i (s⁻¹ * s') ∈ V := by
      have : i (s⁻¹ * s') = (d⁻¹ * i s)⁻¹ * (d⁻¹ * i s') := by
        rw [map_mul, map_inv]
        group
      rw [this]
      exact V.mul_mem (V.inv_mem h1) h2
    have h4 := hχ _ h3
    rw [map_mul, map_inv, inv_mul_eq_one] at h4
    exact h4
  choose f hf using hex
  refine ⟨{ toFun := fun d => χ (f d), map_one' := ?_, map_mul' := ?_ }, ?_, ?_⟩
  · show χ (f 1) = 1
    rw [← χ.map_one]
    exact key 1 _ _ (hf 1) (by simp [V.one_mem])
  · intro d1 d2
    show χ (f (d1 * d2)) = χ (f d1) * χ (f d2)
    rw [← map_mul]
    apply key (d1 * d2) _ _ (hf _)
    have e : (d1 * d2)⁻¹ * i (f d1 * f d2) = (d2⁻¹ * (d1⁻¹ * i (f d1)) * d2⁻¹⁻¹) * (d2⁻¹ * i (f d2)) := by
      rw [map_mul]
      group
    rw [e]
    exact V.mul_mem (‹V.Normal›.conj_mem _ (hf d1) _) (hf d2)
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{y : D | x⁻¹ * y ∈ V}, hV.preimage (continuous_const.mul continuous_id), by simp [V.one_mem], ?_⟩
    intro y hy
    show χ (f y) = χ (f x)
    symm
    apply key x _ _ (hf x)
    have e : x⁻¹ * i (f y) = (x⁻¹ * y) * (y⁻¹ * i (f y)) := by group
    rw [e]
    exact V.mul_mem hy (hf y)
  · intro s
    show χ (f (i s)) = χ s
    exact key (i s) _ _ (hf _) (by simp [V.one_mem])

/- English proof (translation)
Establish `hlift : ∀ y : D, ∃ s, P (i s) = P y`. Introduce `y`. Take `⟨s, hs⟩` from `hi.exists_mem_open (hP.isOpen_fiber (P y)) ⟨y, rfl⟩`. Conclude with `⟨s, hs⟩`. Establish `hcomm : ∀ y z : D, P y * P z = P z * P y`.

Introduce `y z`. Take `⟨s, hs⟩` from `hlift y`. Take `⟨t, ht⟩` from `hlift z`. Rewrite using `[← hs, ← ht]`. Conclude with `hc s t`.

Establish `hle : commutator D ≤ P.ker`. Rewrite using `[commutator, Subgroup.commutator_le]`. Introduce `g1 _ g2 _`. Rewrite using `[MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]`. Conclude with `hcomm g1 g2`.

Conclude with `Subgroup.topologicalClosure_minimal _ hle (hP.isClosed_fiber 1) hx`.
-/
private theorem locallyConstant_hom_trivial_on_commutator_closure {D W C : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group W]
    [Group C] (i : W →* D) (hi : DenseRange i) (P : D →* C) (hP : IsLocallyConstant P)
    (hc : ∀ s t, P (i s) * P (i t) = P (i t) * P (i s)) (x : D)
    (hx : x ∈ (commutator D).topologicalClosure) : P x = 1 := by
  have hlift : ∀ y : D, ∃ s, P (i s) = P y := by
    intro y
    obtain ⟨s, hs⟩ := hi.exists_mem_open (hP.isOpen_fiber (P y)) ⟨y, rfl⟩
    exact ⟨s, hs⟩
  have hcomm : ∀ y z : D, P y * P z = P z * P y := by
    intro y z
    obtain ⟨s, hs⟩ := hlift y
    obtain ⟨t, ht⟩ := hlift z
    rw [← hs, ← ht]
    exact hc s t
  have hle : commutator D ≤ P.ker := by
    rw [commutator, Subgroup.commutator_le]
    intro g1 _ g2 _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm g1 g2
  exact Subgroup.topologicalClosure_minimal _ hle (hP.isClosed_fiber 1) hx

include h in

/- English proof (translation)
Take `⟨φ0, hφ0⟩ : ∃ φ : Weil h, deg φ = 1` from `⟨frob h, deg_frob⟩`. Establish `hnpos : 0 < Nat.card B` using `Nat.card_pos`. Establish `hkpos : 0 < M * Nat.card B` using `Nat.mul_pos hM hnpos`. Take `⟨ζ, hζ⟩` from `GlobalTheory.T.exists_rootOfUnity_fixed_dvd_weilGroupDegree F Ω A w h (M * Nat.card B) hkpos`. Use `haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)`.

Take `⟨H, hH⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin F {ζ})) (Subgroup.one_mem _)`. Set `Hs : Subgroup (G F Ω)` to `(H.toOpenSubgroup : Subgroup (G F Ω))`. Use `haveI hHn : Hs.Normal := H.isNormal'`. Establish `hHo : IsOpen (Hs : Set (G F Ω))` using `H.toOpenSubgroup.isOpen`. Establish `hHfix : ∀ x : G F Ω, x ∈ Hs → x ζ = ζ`.

Introduce `x hx`. Conclude with `((IntermediateField.mem_fixingSubgroup_iff _ x).mp (hH hx)) ζ (IntermediateField.mem_adjoin_simple_self F ζ)`. Set `V : Subgroup (Dec (F` to `F) A) := Hs.subgroupOf (Dec (F := F) A)`. Use `haveI : V.Normal := hHn.subgroupOf _`. Establish `hVo : IsOpen (V : Set (Dec (F` using `F) A)) := hHo.preimage continuous_subtype_val`.

Establish `hi : DenseRange (Subgroup.inclusion (Weil_le_Dec h))` using `weil_group_dense_in_galois_group F Ω w A h`. Set `χd : Weil h →* Multiplicative (ZMod (M * Nat.card B))` to `(AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod (M * Nat.card B)))).comp (degHom h)`. Establish `hχd : ∀ s, χd s = Multiplicative.ofAdd ((deg s : ℤ) : ZMod (M * Nat.card B))`. Introduce `s`. Use `show Multiplicative.ofAdd (Int.castAddHom (ZMod (M * Nat.card B)) (Multiplicative.toAdd (degHom h s))) = _`.

Rewrite using `[degHom_apply]`. Both sides reduce to the same expression. Take `⟨ψ, hψlc, hψ⟩` from `ext_lc (Subgroup.inclusion (Weil_le_Dec h)) hi χd V hVo (by`. Introduce `s hs`. Rewrite using `[hχd, ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Conclude with `hζ s (hHfix _ (Subgroup.mem_subgroupOf.mp hs)))`. Establish `hχW : ∀ s : Weil h, χ (Subgroup.inclusion (Weil_le_Dec h) s) = χ (Subgroup.inclusion (Weil_le_Dec h) φ0) ^ deg s`. Introduce `s`. Take `⟨τ, hτ⟩` from `exists_eq_zpow_mul hφ0 s`. Use `conv_lhs => rw [hτ]`.

Rewrite using `[map_mul, map_mul, map_zpow, map_zpow, hI (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h τ)) τ.2, mul_one]`. Establish `hc1 : ∀ s t : Weil h, χ (Subgroup.inclusion (Weil_le_Dec h) s) * χ (Subgroup.inclusion (Weil_le_Dec h) t) = χ (Subgroup.inclusion (Weil_le_Dec h) t) * χ (Subgroup.inclusion (Weil_le_Dec h) s)`. Introduce `s t`. Rewrite using `[hχW s, hχW t]`. Conclude with `((Commute.refl _).zpow_zpow _ _).eq`.

Establish `hc2 : ∀ s t : Weil h, ψ (Subgroup.inclusion (Weil_le_Dec h) s) * ψ (Subgroup.inclusion (Weil_le_Dec h) t) = ψ (Subgroup.inclusion (Weil_le_Dec h) t) * ψ (Subgroup.inclusion (Weil_le_Dec h) s)` using `fun s t => mul_comm _ _`. Establish `h1` using `locallyConstant_hom_trivial_on_commutator_closure _ hi χ hχ hc1 _ hg`. Establish `h2` using `locallyConstant_hom_trivial_on_commutator_closure _ hi ψ hψlc hc2 _ hg`. Choose the witnesses or unpack the hypotheses as in `⟨σ, hσ1, hσ2⟩ : ∃ σ : Weil h, χ (Subgroup.inclusion (Weil_le_Dec h) σ) = χ g ∧ ψ (Subgroup.inclusion (Weil_le_Dec h) σ) = ψ g := by`. Take `⟨σ, hσ⟩` from `hi.exists_mem_open ((hχ.isOpen_fiber (χ g)).inter (hψlc.isOpen_fiber (ψ g))) ⟨g, rfl, rfl⟩`.

Conclude with `⟨σ, hσ.1, hσ.2⟩`. Rewrite `h2` using `[map_pow, ← hσ2, hψ, hχd, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul]`. Establish `h3 : (((M * deg σ : ℤ)) : ZMod (M * Nat.card B)) = 0`. Use `push_cast`. Conclude with `h2`.

Rewrite `h3` using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Establish `hM0 : (M : ℤ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `h4 : (Nat.card B : ℤ) ∣ deg σ`. Move the coercions through the operations in `at h3`. Conclude with `(mul_dvd_mul_iff_left hM0).mp h3`.

Take `⟨m, hm⟩` from `h4`. Rewrite using `[← hσ1, hχW, hm, zpow_mul, zpow_natCast, pow_card_eq_one', one_zpow]`.
-/
theorem char_tors {B : Type} [Group B] [Finite B] (χ : Dec (F := F) A →* B) (hχ : IsLocallyConstant χ)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 1) (g : Dec (F := F) A) (M : ℕ) (hM : 0 < M)
    (hg : g ^ M ∈ (commutator (Dec (F := F) A)).topologicalClosure) : χ g = 1 := by
  obtain ⟨φ0, hφ0⟩ : ∃ φ : Weil h, deg φ = 1 := ⟨frob h, deg_frob⟩
  have hnpos : 0 < Nat.card B := Nat.card_pos
  have hkpos : 0 < M * Nat.card B := Nat.mul_pos hM hnpos
  obtain ⟨ζ, hζ⟩ := GlobalTheory.T.exists_rootOfUnity_fixed_dvd_weilGroupDegree F Ω A w h (M * Nat.card B) hkpos
  haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin F {ζ})) (Subgroup.one_mem _)
  let Hs : Subgroup (G F Ω) := (H.toOpenSubgroup : Subgroup (G F Ω))
  haveI hHn : Hs.Normal := H.isNormal'
  have hHo : IsOpen (Hs : Set (G F Ω)) := H.toOpenSubgroup.isOpen
  have hHfix : ∀ x : G F Ω, x ∈ Hs → x ζ = ζ := by
    intro x hx
    exact ((IntermediateField.mem_fixingSubgroup_iff _ x).mp (hH hx)) ζ
      (IntermediateField.mem_adjoin_simple_self F ζ)
  let V : Subgroup (Dec (F := F) A) := Hs.subgroupOf (Dec (F := F) A)
  haveI : V.Normal := hHn.subgroupOf _
  have hVo : IsOpen (V : Set (Dec (F := F) A)) := hHo.preimage continuous_subtype_val
  have hi : DenseRange (Subgroup.inclusion (Weil_le_Dec h)) := weil_group_dense_in_galois_group F Ω w A h
  let χd : Weil h →* Multiplicative (ZMod (M * Nat.card B)) :=
    (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod (M * Nat.card B)))).comp (degHom h)
  have hχd : ∀ s, χd s = Multiplicative.ofAdd ((deg s : ℤ) : ZMod (M * Nat.card B)) := by
    intro s
    show Multiplicative.ofAdd (Int.castAddHom (ZMod (M * Nat.card B)) (Multiplicative.toAdd (degHom h s))) = _
    rw [degHom_apply]
    rfl
  obtain ⟨ψ, hψlc, hψ⟩ := ext_lc (Subgroup.inclusion (Weil_le_Dec h)) hi χd V hVo (by
    intro s hs
    rw [hχd, ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hζ s (hHfix _ (Subgroup.mem_subgroupOf.mp hs)))
  have hχW : ∀ s : Weil h, χ (Subgroup.inclusion (Weil_le_Dec h) s) =
      χ (Subgroup.inclusion (Weil_le_Dec h) φ0) ^ deg s := by
    intro s
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul hφ0 s
    conv_lhs => rw [hτ]
    rw [map_mul, map_mul, map_zpow, map_zpow, hI (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h τ)) τ.2, mul_one]
  have hc1 : ∀ s t : Weil h, χ (Subgroup.inclusion (Weil_le_Dec h) s) * χ (Subgroup.inclusion (Weil_le_Dec h) t) =
      χ (Subgroup.inclusion (Weil_le_Dec h) t) * χ (Subgroup.inclusion (Weil_le_Dec h) s) := by
    intro s t
    rw [hχW s, hχW t]
    exact ((Commute.refl _).zpow_zpow _ _).eq
  have hc2 : ∀ s t : Weil h, ψ (Subgroup.inclusion (Weil_le_Dec h) s) * ψ (Subgroup.inclusion (Weil_le_Dec h) t) =
      ψ (Subgroup.inclusion (Weil_le_Dec h) t) * ψ (Subgroup.inclusion (Weil_le_Dec h) s) :=
    fun s t => mul_comm _ _
  have h1 := locallyConstant_hom_trivial_on_commutator_closure _ hi χ hχ hc1 _ hg
  have h2 := locallyConstant_hom_trivial_on_commutator_closure _ hi ψ hψlc hc2 _ hg
  obtain ⟨σ, hσ1, hσ2⟩ : ∃ σ : Weil h, χ (Subgroup.inclusion (Weil_le_Dec h) σ) = χ g ∧
      ψ (Subgroup.inclusion (Weil_le_Dec h) σ) = ψ g := by
    obtain ⟨σ, hσ⟩ := hi.exists_mem_open ((hχ.isOpen_fiber (χ g)).inter (hψlc.isOpen_fiber (ψ g)))
      ⟨g, rfl, rfl⟩
    exact ⟨σ, hσ.1, hσ.2⟩
  rw [map_pow, ← hσ2, hψ, hχd, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul] at h2
  have h3 : (((M * deg σ : ℤ)) : ZMod (M * Nat.card B)) = 0 := by
    push_cast
    exact h2
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have h4 : (Nat.card B : ℤ) ∣ deg σ := by
    push_cast at h3
    exact (mul_dvd_mul_iff_left hM0).mp h3
  obtain ⟨m, hm⟩ := h4
  rw [← hσ1, hχW, hm, zpow_mul, zpow_natCast, pow_card_eq_one', one_zpow]

include h in

/- English proof (translation)
Establish `hfg : (IsLocalRing.maximalIdeal R).FG` using `IsNoetherian.noetherian _`. Use `haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) := ‹Finite (IsLocalRing.ResidueField R)›`. Establish `hN : ∀ N : ℕ, Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) (ψ g : R) = Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) (ψ' g : R)`. Introduce `N`. Use `haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ N) := Ideal.finite_quotient_pow hfg N`.

Set `mkN : R →* R ⧸ IsLocalRing.maximalIdeal R ^ N` to `(Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N)).toMonoidHom`. Set `u : Dec (F` to `F) A →* (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ := (Units.map mkN).comp ψ`. Set `u' : Dec (F` to `F) A →* (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ := (Units.map mkN).comp ψ'`. Establish `hu : IsLocallyConstant u` using `IsLocallyConstant.desc _ Units.val (hψ N) (fun _ _ e => Units.ext e)`. Establish `hu' : IsLocallyConstant u'` using `IsLocallyConstant.desc _ Units.val (hψ' N) (fun _ _ e => Units.ext e)`.

Establish `hχN : IsLocallyConstant (u * u'⁻¹)` using `hu.mul hu'.inv`. Establish `hres` using `char_tors h (u * u'⁻¹) hχN (by`. Introduce `x hx`. Use `show u x * (u' x)⁻¹ = 1`. Establish `e : u x = u' x` using `by show Units.map mkN (ψ x) = Units.map mkN (ψ' x)`.

Rewrite using `[hI x hx]`. Rewrite using `[e, mul_inv_cancel]) g M hM hg`. Establish `e2 : u g = u' g`. Establish `: u g * (u' g)⁻¹ = 1` using `hres`. Conclude with `mul_inv_eq_one.mp this`.

Conclude with `congrArg Units.val e2`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal R)]`. Introduce `n`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`.

Conclude with `Ideal.Quotient.eq.mp (hN n)`.
-/
theorem eq_on_tors {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Finite (IsLocalRing.ResidueField R)] (ψ ψ' : Dec (F := F) A →* Rˣ)
    (hψ : Alg.AdicCont (IsLocalRing.maximalIdeal R) fun g => (ψ g : R))
    (hψ' : Alg.AdicCont (IsLocalRing.maximalIdeal R) fun g => (ψ' g : R))
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → ψ g = ψ' g) (g : Dec (F := F) A) (M : ℕ) (hM : 0 < M)
    (hg : g ^ M ∈ (commutator (Dec (F := F) A)).topologicalClosure) : ψ g = ψ' g := by
  have hfg : (IsLocalRing.maximalIdeal R).FG := IsNoetherian.noetherian _
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) := ‹Finite (IsLocalRing.ResidueField R)›
  have hN : ∀ N : ℕ, Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) (ψ g : R) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) (ψ' g : R) := by
    intro N
    haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ N) := Ideal.finite_quotient_pow hfg N
    let mkN : R →* R ⧸ IsLocalRing.maximalIdeal R ^ N :=
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N)).toMonoidHom
    let u : Dec (F := F) A →* (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ := (Units.map mkN).comp ψ
    let u' : Dec (F := F) A →* (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ := (Units.map mkN).comp ψ'
    have hu : IsLocallyConstant u :=
      IsLocallyConstant.desc _ Units.val (hψ N) (fun _ _ e => Units.ext e)
    have hu' : IsLocallyConstant u' :=
      IsLocallyConstant.desc _ Units.val (hψ' N) (fun _ _ e => Units.ext e)
    have hχN : IsLocallyConstant (u * u'⁻¹) := hu.mul hu'.inv
    have hres := char_tors h (u * u'⁻¹) hχN (by
      intro x hx
      show u x * (u' x)⁻¹ = 1
      have e : u x = u' x := by
        show Units.map mkN (ψ x) = Units.map mkN (ψ' x)
        rw [hI x hx]
      rw [e, mul_inv_cancel]) g M hM hg
    have e2 : u g = u' g := by
      have : u g * (u' g)⁻¹ = 1 := hres
      exact mul_inv_eq_one.mp this
    exact congrArg Units.val e2
  apply Units.ext
  rw [IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal R)]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact Ideal.Quotient.eq.mp (hN n)

end UpperTheory.V.Hi.JEx
