import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

noncomputable section
open CategoryTheory AlgebraicGeometry MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.JetSer

section Val
variable {A : Type} [CommRing A] {X : Scheme.{0}}

def fnValHom (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (p.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

/- English proof (translation)
Unfold `fnVal`. Rewrite using `[dif_pos h]`. Both sides reduce to the same expression.
-/
theorem fnVal_eq_fnValHom (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(X, U)) :
    fnVal p U f = fnValHom p U h f := by
  unfold fnVal
  rw [dif_pos h]
  rfl

/- English proof (translation)
Introduce `z _` and use `by have : r z ∈ p ⁻¹ᵁ U := h trivial simpa using this`.
-/
theorem top_le_preimage_comp {T T' : Scheme.{0}} (r : T' ⟶ T) (p : T ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    ⊤ ≤ (r ≫ p) ⁻¹ᵁ U := fun z _ => by
  have : r z ∈ p ⁻¹ᵁ U := h trivial
  simpa using this

/- English proof (translation)
Establish `h'` using `top_le_preimage_comp (Spec.map (CommRingCat.ofHom ψ)) p U h`. Rewrite using `[fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]`. Establish `e : (Spec.map (CommRingCat.ofHom ψ) ≫ p).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom = (p.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) ≫ CommRingCat.ofHom ψ`. Rewrite using `[Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc, ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom ψ)) p U ⊤ ⊤ h le_top]`. Use `congr 2`.

Unfold `fnValHom`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem fnVal_specMap {B : Type} [CommRing B] (ψ : A →+* B) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(X, U)) :
    fnVal (Spec.map (CommRingCat.ofHom ψ) ≫ p) U f = ψ (fnVal p U f) := by
  have h' := top_le_preimage_comp (Spec.map (CommRingCat.ofHom ψ)) p U h
  rw [fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]
  have e : (Spec.map (CommRingCat.ofHom ψ) ≫ p).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      (p.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) ≫ CommRingCat.ofHom ψ := by
    rw [Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom ψ)) p U ⊤ ⊤ h le_top]
    congr 2
  unfold fnValHom
  rw [e]
  rfl

/- English proof (translation)
Establish `h' : ⊤ ≤ (p ≫ q) ⁻¹ᵁ V` using `fun z _ => by`. Establish `: p z ∈ q ⁻¹ᵁ V` using `hUV (h trivial)`. Simplify using `using this`. Use `⟨h', ?_⟩` and prove the remaining obligations. Rewrite using `[fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]`.

Unfold `fnValHom`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE p q V U ⊤ hUV h]`. Both sides reduce to the same expression.
-/
theorem fnVal_comp {Y : Scheme.{0}} (p : Spec (CommRingCat.of A) ⟶ X) (q : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (hUV : U ≤ q ⁻¹ᵁ V) (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(Y, V)) :
    ⊤ ≤ (p ≫ q) ⁻¹ᵁ V ∧ fnVal (p ≫ q) V f = fnVal p U ((q.appLE V U hUV).hom f) := by
  have h' : ⊤ ≤ (p ≫ q) ⁻¹ᵁ V := fun z _ => by
    have : p z ∈ q ⁻¹ᵁ V := hUV (h trivial)
    simpa using this
  refine ⟨h', ?_⟩
  rw [fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]
  unfold fnValHom
  rw [← Scheme.Hom.appLE_comp_appLE p q V U ⊤ hUV h]
  rfl

/- English proof (translation)
Establish `h' : ⊤ ≤ p ⁻¹ᵁ V` using `fun z _ => hUV (h trivial)`. Use `⟨h', ?_⟩` and prove the remaining obligations. Rewrite using `[fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]`. Unfold `fnValHom`. Rewrite using `[← Scheme.Hom.map_appLE p h (homOfLE hUV).op]`.

Both sides reduce to the same expression.
-/
theorem fnVal_res (p : Spec (CommRingCat.of A) ⟶ X) (U V : X.Opens) (hUV : U ≤ V) (h : ⊤ ≤ p ⁻¹ᵁ U)
    (f : Γ(X, V)) :
    ⊤ ≤ p ⁻¹ᵁ V ∧ fnVal p V f = fnVal p U ((X.presheaf.map (homOfLE hUV).op).hom f) := by
  have h' : ⊤ ≤ p ⁻¹ᵁ V := fun z _ => hUV (h trivial)
  refine ⟨h', ?_⟩
  rw [fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]
  unfold fnValHom
  rw [← Scheme.Hom.map_appLE p h (homOfLE hUV).op]
  rfl

/- English proof (translation)
Introduce `z _`. Establish `hker : RingHom.ker q ≤ z.asIdeal` using `fun a ha => by`. Take `⟨n, hn⟩` from `hn a ha`. Conclude with `z.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)`. Use `z.isPrime` as an intermediate fact.

Establish `hprime : (z.asIdeal.map q).IsPrime` using `Ideal.map_isPrime_of_surjective hq hker`. Set `z₀ : ↥(Spec (CommRingCat.of B))` to `(⟨z.asIdeal.map q, hprime⟩ : PrimeSpectrum B)`. Establish `hz : (Spec.map (CommRingCat.ofHom q)) z₀ = z`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap q (Ideal.map q z.asIdeal) = z.asIdeal`.

Rewrite using `[Ideal.comap_map_of_surjective' q hq, sup_eq_left.mpr hker]`. Establish `h0 : z₀ ∈ (Spec.map (CommRingCat.ofHom q) ≫ p) ⁻¹ᵁ U` using `h trivial`. Rewrite using `[← hz]`. Simplify using `using h0`.
-/
theorem top_le_preimage_of_nil {B : Type} [CommRing B] (q : A →+* B) (hq : Function.Surjective q)
    (hn : ∀ a ∈ RingHom.ker q, IsNilpotent a) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom q) ≫ p) ⁻¹ᵁ U) : ⊤ ≤ p ⁻¹ᵁ U := by
  intro z _
  have hker : RingHom.ker q ≤ z.asIdeal := fun a ha => by
    obtain ⟨n, hn⟩ := hn a ha
    exact z.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
  have := z.isPrime
  have hprime : (z.asIdeal.map q).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  let z₀ : ↥(Spec (CommRingCat.of B)) := (⟨z.asIdeal.map q, hprime⟩ : PrimeSpectrum B)
  have hz : (Spec.map (CommRingCat.ofHom q)) z₀ = z := by
    apply PrimeSpectrum.ext
    change Ideal.comap q (Ideal.map q z.asIdeal) = z.asIdeal
    rw [Ideal.comap_map_of_surjective' q hq, sup_eq_left.mpr hker]
  have h0 : z₀ ∈ (Spec.map (CommRingCat.ofHom q) ≫ p) ⁻¹ᵁ U := h trivial
  rw [← hz]
  simpa using h0

end Val

section Jet
variable {R : Type} [CommRing R] {κ : Type}

/- English proof (translation)
Introduce `y`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `⟨Ideal.Quotient.mk _ a, rfl⟩`.
-/
theorem jetTruncR_surjective (m : ℕ) : Function.Surjective (jetTruncR R κ m) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

/- English proof (translation)
Establish `e : (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1)` using `jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR (m + 1) j).symm`. Establish `ha' : jetTruncR R κ m a = 0` using `ha`. Establish `h1 : a ∈ RingHom.ker (jetAug R κ (m + 1))`. Rewrite using `[RingHom.mem_ker, ← e, AlgHom.comp_apply, ha', map_zero]`. Use `⟨m + 1 + 1, ?_⟩` and prove the remaining obligations.

Use `Ideal.pow_mem_pow h1 (m + 1 + 1)` as an intermediate fact. Rewrite `this` using `[ker_jetAug_pow, Ideal.mem_bot]`. Then use the resulting hypothesis.
-/
theorem isNilpotent_of_mem_ker_jetTruncR (m : ℕ) (a : JetR R κ (m + 1))
    (ha : a ∈ RingHom.ker (jetTruncR R κ m).toRingHom) : IsNilpotent a := by
  have e : (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) :=
    jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR (m + 1) j).symm
  have ha' : jetTruncR R κ m a = 0 := ha
  have h1 : a ∈ RingHom.ker (jetAug R κ (m + 1)) := by
    rw [RingHom.mem_ker, ← e, AlgHom.comp_apply, ha', map_zero]
  refine ⟨m + 1 + 1, ?_⟩
  have := Ideal.pow_mem_pow h1 (m + 1 + 1)
  rwa [ker_jetAug_pow, Ideal.mem_bot] at this

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact h`. Consider the case `succ m ih`. Rewrite `ih` using `[← hp m]`. Conclude with `top_le_preimage_of_nil (jetTruncR R κ m).toRingHom (jetTruncR_surjective m) (isNilpotent_of_mem_ker_jetTruncR m) _ U ih`.
-/
theorem top_le_preimage_jet {X : Scheme.{0}} (p : ∀ m : ℕ, Spec (CommRingCat.of (JetR R κ m)) ⟶ X)
    (hp : ∀ m, (spMap (jetTruncR R κ m)).left ≫ p (m + 1) = p m) (U : X.Opens) (h : ⊤ ≤ p 0 ⁻¹ᵁ U) (m : ℕ) :
    ⊤ ≤ p m ⁻¹ᵁ U := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [← hp m] at ih
    exact top_le_preimage_of_nil (jetTruncR R κ m).toRingHom (jetTruncR_surjective m)
      (isNilpotent_of_mem_ker_jetTruncR m) _ U ih

end Jet

/- English proof (translation)
Introduce `hJ R _ κ _ X p hp U h0`. Establish `hU` using `top_le_preimage_jet p hp U h0`. Take `⟨hτ, -, hinj, hex, -⟩` from `hJ R κ`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : ∀ f : Γ(X, U), ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = fnValHom (p m) U (hU m) f`.

Introduce `f`. Use `hex (fun m => fnValHom (p m) U (hU m) f) fun m => ?_` and prove the remaining obligations. Use `fnVal_specMap (jetTruncR R κ m).toRingHom (p (m + 1)) U (hU _) f` as an intermediate fact. Rewrite `this` using `[← spMap_left, hp m, fnVal_eq_fnValHom _ _ (hU _), fnVal_eq_fnValHom _ _ (hU _)]`. Conclude with `this.symm`.

Use `choose T hT using hc`. Use `choose τ hτ₁ hτ₂ using hτ`. Use `⟨{ toFun := T map_one' := hinj _ _ fun m => by rw [hT, ← hτ₁, map_one, map_one] map_mul' := fun a b => hinj _ _ fun m => by` and prove the remaining obligations. Rewrite using `[hT, ← hτ₁, map_mul, map_mul, hτ₁, hτ₁, hT, hT]`. Use the proof step `map_zero' := hinj _ _ fun m => by rw [hT, ← hτ₁, map_zero, map_zero]`.

Use the proof step `map_add' := fun a b => hinj _ _ fun m => by`. Rewrite using `[hT, ← hτ₁, map_add, map_add, hτ₁, hτ₁, hT, hT] }, fun f g => ⟨fun H => ?_, fun H m => ?_⟩⟩`. Conclude with `hinj _ _ fun m => by`. Rewrite using `[← (H m).2, fnVal_eq_fnValHom _ _ (hU m)]`. Conclude with `(hT f m).symm`.

Use `⟨hU m, ?_⟩` and prove the remaining obligations. Rewrite using `[H, fnVal_eq_fnValHom _ _ (hU m)]`. Conclude with `(hT f m).symm`. Introduce `V h f g`. Use `forall_congr' fun m => ?_` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `fnVal_res (p m) U V h (hU m) f`. Rewrite using `[h2]`. Conclude with `⟨fun H => ⟨hU m, H.2⟩, fun H => ⟨h1, H.2⟩⟩`. Introduce `Y q V h f g`. Use `forall_congr' fun m => ?_` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `fnVal_comp (p m) q U V h (hU m) f`. Rewrite using `[h2]`. Conclude with `⟨fun H => ⟨hU m, H.2⟩, fun H => ⟨h1, H.2⟩⟩`. Introduce `κ' _ b ψ hb hψ f g H m`. Use `⟨top_le_preimage_comp _ _ U (hU m), ?_⟩` and prove the remaining obligations.

Use `fnVal_specMap (ψ m).toRingHom (p m) U (hU m) f` as an intermediate fact. Rewrite `this` using `[(H m).2]`. Conclude with `this.trans (((hJ R κ').2.2.2.2 κ b hb m).2 (ψ m) (hψ m) g)`.
-/
theorem serSt_of_jetAlgSt : JetAlgSt → SerSt := by
  intro hJ R _ κ _ X p hp U h0
  have hU := top_le_preimage_jet p hp U h0
  obtain ⟨hτ, -, hinj, hex, -⟩ := hJ R κ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : ∀ f : Γ(X, U), ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = fnValHom (p m) U (hU m) f := by
      intro f
      refine hex (fun m => fnValHom (p m) U (hU m) f) fun m => ?_
      have := fnVal_specMap (jetTruncR R κ m).toRingHom (p (m + 1)) U (hU _) f
      rw [← spMap_left, hp m, fnVal_eq_fnValHom _ _ (hU _), fnVal_eq_fnValHom _ _ (hU _)] at this
      exact this.symm
    choose T hT using hc
    choose τ hτ₁ hτ₂ using hτ
    refine ⟨{ toFun := T
              map_one' := hinj _ _ fun m => by rw [hT, ← hτ₁, map_one, map_one]
              map_mul' := fun a b => hinj _ _ fun m => by
                rw [hT, ← hτ₁, map_mul, map_mul, hτ₁, hτ₁, hT, hT]
              map_zero' := hinj _ _ fun m => by rw [hT, ← hτ₁, map_zero, map_zero]
              map_add' := fun a b => hinj _ _ fun m => by
                rw [hT, ← hτ₁, map_add, map_add, hτ₁, hτ₁, hT, hT] }, fun f g => ⟨fun H => ?_, fun H m => ?_⟩⟩
    · exact hinj _ _ fun m => by
        rw [← (H m).2, fnVal_eq_fnValHom _ _ (hU m)]
        exact (hT f m).symm
    · refine ⟨hU m, ?_⟩
      rw [H, fnVal_eq_fnValHom _ _ (hU m)]
      exact (hT f m).symm
  · intro V h f g
    refine forall_congr' fun m => ?_
    obtain ⟨h1, h2⟩ := fnVal_res (p m) U V h (hU m) f
    rw [h2]
    exact ⟨fun H => ⟨hU m, H.2⟩, fun H => ⟨h1, H.2⟩⟩
  · intro Y q V h f g
    refine forall_congr' fun m => ?_
    obtain ⟨h1, h2⟩ := fnVal_comp (p m) q U V h (hU m) f
    rw [h2]
    exact ⟨fun H => ⟨hU m, H.2⟩, fun H => ⟨h1, H.2⟩⟩
  · intro κ' _ b ψ hb hψ f g H m
    refine ⟨top_le_preimage_comp _ _ U (hU m), ?_⟩
    have := fnVal_specMap (ψ m).toRingHom (p m) U (hU m) f
    rw [(H m).2] at this
    exact this.trans (((hJ R κ').2.2.2.2 κ b hb m).2 (ψ m) (hψ m) g)

end GlobalTheory.JetSer
