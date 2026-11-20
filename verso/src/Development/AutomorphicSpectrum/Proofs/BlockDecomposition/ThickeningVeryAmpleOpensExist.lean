import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

/- English proof (translation)
The claim follows from `Scheme.basicOpen_res X f (homOfLE h).op`.
-/
theorem basicOpen_rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) :
    X.basicOpen (rs X h f) = V ⊓ X.basicOpen f :=
  Scheme.basicOpen_res X f (homOfLE h).op

/- English proof (translation)
The claim follows from `TopologicalSpace.Opens.mem_iSup`.
-/
theorem mem_nonzeroLocus_iff {X : Scheme.{0}} {H : LB X} (s : LB.Sec H) (x : X) :
    x ∈ nonzeroLocus s ↔ ∃ k, x ∈ X.basicOpen (s.f k) :=
  TopologicalSpace.Opens.mem_iSup

/- English proof (translation)
Establish `key : ∀ (k : H.ι) (x : X), x ∈ nonzeroLocus a → x ∈ H.U k → (x ∈ X.basicOpen (b.f k) ↔ x ∈ X.basicOpen r ∧ x ∈ X.basicOpen (a.f k))`. Introduce `k x hxa hxk`. Establish `h` using `congrArg X.basicOpen (hr k)`. Rewrite `h` using `[Scheme.basicOpen_mul, basicOpen_rs, basicOpen_rs, basicOpen_rs]`. Establish `hx : x ∈ nonzeroLocus a ⊓ H.U k` using `⟨hxa, hxk⟩`.

Prove the components needed by the constructor for the conclusion. Introduce `hb`. Establish `: x ∈ (nonzeroLocus a ⊓ H.U k) ⊓ X.basicOpen (b.f k)` using `⟨hx, hb⟩`. Rewrite `this` using `[h]`. Conclude with `⟨this.1.2, this.2.2⟩`.

Introduce and unpack `⟨h₁, h₂⟩`. Establish `: x ∈ (nonzeroLocus a ⊓ H.U k ⊓ X.basicOpen r) ⊓ (nonzeroLocus a ⊓ H.U k ⊓ X.basicOpen (a.f k))` using `⟨⟨hx, h₁⟩, ⟨hx, h₂⟩⟩`. Rewrite `this` using `[← h]`. Conclude with `this.2`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `x hx`. Establish `hxa : x ∈ nonzeroLocus a` using `X.basicOpen_le r hx`. Take `⟨k, hk⟩` from `(mem_nonzeroLocus_iff a x).1 hxa`. Conclude with `⟨hxa, (mem_nonzeroLocus_iff b x).2 ⟨k, (key k x hxa (X.basicOpen_le _ hk)).2 ⟨hx, hk⟩⟩⟩`. Introduce and unpack `x ⟨hxa, hxb⟩`.

Take `⟨k, hk⟩` from `(mem_nonzeroLocus_iff b x).1 hxb`. Conclude with `((key k x hxa (X.basicOpen_le _ hk)).1 hk).1`.
-/
theorem basicOpen_eq_inf_nonzeroLocus {X : Scheme.{0}} {H : LB X} (a b : LB.Sec H)
    (r : Γ(X, nonzeroLocus a))
    (hr : ∀ k, rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) (b.f k) =
      rs X (inf_le_left : nonzeroLocus a ⊓ H.U k ≤ nonzeroLocus a) r *
        rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) (a.f k)) :
    X.basicOpen r = nonzeroLocus a ⊓ nonzeroLocus b := by
  have key : ∀ (k : H.ι) (x : X), x ∈ nonzeroLocus a → x ∈ H.U k →
      (x ∈ X.basicOpen (b.f k) ↔ x ∈ X.basicOpen r ∧ x ∈ X.basicOpen (a.f k)) := by
    intro k x hxa hxk
    have h := congrArg X.basicOpen (hr k)
    rw [Scheme.basicOpen_mul, basicOpen_rs, basicOpen_rs, basicOpen_rs] at h
    have hx : x ∈ nonzeroLocus a ⊓ H.U k := ⟨hxa, hxk⟩
    constructor
    · intro hb
      have : x ∈ (nonzeroLocus a ⊓ H.U k) ⊓ X.basicOpen (b.f k) := ⟨hx, hb⟩
      rw [h] at this
      exact ⟨this.1.2, this.2.2⟩
    · rintro ⟨h₁, h₂⟩
      have : x ∈ (nonzeroLocus a ⊓ H.U k ⊓ X.basicOpen r) ⊓
          (nonzeroLocus a ⊓ H.U k ⊓ X.basicOpen (a.f k)) := ⟨⟨hx, h₁⟩, ⟨hx, h₂⟩⟩
      rw [← h] at this
      exact this.2
  apply le_antisymm
  · intro x hx
    have hxa : x ∈ nonzeroLocus a := X.basicOpen_le r hx
    obtain ⟨k, hk⟩ := (mem_nonzeroLocus_iff a x).1 hxa
    exact ⟨hxa, (mem_nonzeroLocus_iff b x).2
      ⟨k, (key k x hxa (X.basicOpen_le _ hk)).2 ⟨hx, hk⟩⟩⟩
  · rintro x ⟨hxa, hxb⟩
    obtain ⟨k, hk⟩ := (mem_nonzeroLocus_iff b x).1 hxb
    exact ((key k x hxa (X.basicOpen_le _ hk)).1 hk).1

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, by simp⟩`. Consider the case `insert j S _ ih`. Take `⟨f, hf⟩` from `ih`. Take `⟨r, hr⟩` from `hi j`.

Use `⟨f * r, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.basicOpen_mul, hf, hr, Finset.iInf_insert]`. Use extensionality with `x`. Simplify using `only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]`. The claim follows by propositional logic.
-/
theorem exists_basicOpen_eq_inf_iInf {X : Scheme.{0}} {H : LB X} {m : ℕ}
    (s : Fin (m + 1) → LB.Sec H) (i : Fin (m + 1))
    (hi : ∀ j, ∃ r : Γ(X, nonzeroLocus (s i)),
      X.basicOpen r = nonzeroLocus (s i) ⊓ nonzeroLocus (s j))
    (S : Finset (Fin (m + 1))) :
    ∃ f : Γ(X, nonzeroLocus (s i)),
      X.basicOpen f = nonzeroLocus (s i) ⊓ ⨅ j ∈ S, nonzeroLocus (s j) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert j S _ ih =>
    obtain ⟨f, hf⟩ := ih
    obtain ⟨r, hr⟩ := hi j
    refine ⟨f * r, ?_⟩
    rw [Scheme.basicOpen_mul, hf, hr, Finset.iInf_insert]
    ext x
    simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
    tauto

/- English proof (translation)
Take `⟨i, hi⟩` from `hS`. Take `⟨hA, r, hr, -⟩` from `h.2 i`. Take `⟨g, hg⟩` from `exists_basicOpen_eq_inf_iInf s i (fun j => ⟨r j, basicOpen_eq_inf_nonzeroLocus (s i) (s j) (r j) (hr j)⟩) S`. Establish `e : ⨅ j ∈ S, nonzeroLocus (s j) = X.basicOpen g`. Rewrite using `[hg]`.

Conclude with `(inf_eq_right.2 (iInf₂_le i hi)).symm`. Rewrite using `[e]`. Conclude with `hA.basicOpen g`.
-/
theorem isAffineOpen_iInf_nonzeroLocus {X : Scheme.{0}} {R : Type} [CommRing R]
    {f : X ⟶ Spec (CommRingCat.of R)} {H : LB X} {m : ℕ} {s : Fin (m + 1) → LB.Sec H}
    (h : VeryAmpleBy f H s) {S : Finset (Fin (m + 1))} (hS : S.Nonempty) :
    IsAffineOpen (⨅ i ∈ S, nonzeroLocus (s i)) := by
  obtain ⟨i, hi⟩ := hS
  obtain ⟨hA, r, hr, -⟩ := h.2 i
  obtain ⟨g, hg⟩ := exists_basicOpen_eq_inf_iInf s i
    (fun j => ⟨r j, basicOpen_eq_inf_nonzeroLocus (s i) (s j) (r j) (hr j)⟩) S
  have e : ⨅ j ∈ S, nonzeroLocus (s j) = X.basicOpen g := by
    rw [hg]
    exact (inf_eq_right.2 (iInf₂_le i hi)).symm
  rw [e]
  exact hA.basicOpen g

/- English proof (translation)
Use `⟨fun (x : PrimeSpectrum A) ↦ ?_⟩` and prove the remaining obligations. Establish `: x ∈ Set.range (PrimeSpectrum.comap g)`. Rewrite using `[_root_.range_comap_of_surjective _ _ hg]`. Take `⟨n, hn⟩` from `hn`. Introduce `a ha`.

Apply `x.isPrime.mem_of_pow_mem n` to reduce the goal to its premises. Establish `: a ^ n ∈ RingHom.ker g ^ n` using `Ideal.pow_mem_pow ha n`. Rewrite `this` using `[hn]`. Rewrite using `[show a ^ n = 0 from this]`. Conclude with `zero_mem _`.

Conclude with `this`.
-/
theorem surjective_spec_of_nilpotent_ker {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : Function.Surjective g) (hn : IsNilpotent (RingHom.ker g)) :
    Surjective (Spec.map (CommRingCat.ofHom g)) := by
  refine ⟨fun (x : PrimeSpectrum A) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap g) := by
    rw [_root_.range_comap_of_surjective _ _ hg]
    obtain ⟨n, hn⟩ := hn
    intro a ha
    apply x.isPrime.mem_of_pow_mem n
    have : a ^ n ∈ RingHom.ker g ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    rw [show a ^ n = 0 from this]
    exact zero_mem _
  exact this

/- English proof (translation)
Use `⟨2, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]`. Express the relevant statement in the definitionally equal form `_ = ⊥`. Rewrite using `[eq_bot_iff, ← Ideal.map_quotient_self (I ^ (e + 1 + 1))]`. Conclude with `Ideal.map_mono (Ideal.pow_le_pow_right (by omega))`.
-/
theorem isNilpotent_ker_factor {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1)))) := by
  refine ⟨2, ?_⟩
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
  change _ = ⊥
  rw [eq_bot_iff, ← Ideal.map_quotient_self (I ^ (e + 1 + 1))]
  exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega))

/- English proof (translation)
Set `h : X ≃ₜ X'` to `(β.isClosedEmbedding.isEmbedding).toHomeomorphOfSurjective β.surjective`. Use `⟨h.opensCongr, fun U => ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Establish `e : h.symm (β x) = x` using `h.symm_apply_apply x`. Simplify using `[h] at e ⊢`.

Rewrite using `[e]`.
-/
theorem exists_orderIso_opens {X X' : Scheme.{0}} (β : X ⟶ X') [IsClosedImmersion β]
    [Surjective β] : ∃ Φ : X.Opens ≃o X'.Opens, ∀ U, β ⁻¹ᵁ Φ U = U := by
  let h : X ≃ₜ X' := (β.isClosedEmbedding.isEmbedding).toHomeomorphOfSurjective β.surjective
  refine ⟨h.opensCongr, fun U => ?_⟩
  ext x
  have e : h.symm (β x) = x := h.symm_apply_apply x
  simp [h] at e ⊢
  rw [e]

/- English proof (translation)
Use `choose Φ hΦ using fun e => exists_orderIso_opens (β e)`. Set `G : ∀ e, (X 0).Opens ≃o (X e).Opens` to `fun e => Nat.rec (OrderIso.refl _) (fun e G => G.trans (Φ e)) e`. Conclude with `⟨G, fun _ => rfl, fun e U => hΦ e (G e U)⟩`.
-/
theorem exists_orderIso_opens_tower (X : ℕ → Scheme.{0}) (β : ∀ e, X e ⟶ X (e + 1))
    [∀ e, IsClosedImmersion (β e)] [∀ e, Surjective (β e)] :
    ∃ G : ∀ e, (X 0).Opens ≃o (X e).Opens, (∀ U, G 0 U = U) ∧
      ∀ e U, β e ⁻¹ᵁ G (e + 1) U = G e U := by
  choose Φ hΦ using fun e => exists_orderIso_opens (β e)
  let G : ∀ e, (X 0).Opens ≃o (X e).Opens := fun e =>
    Nat.rec (OrderIso.refl _) (fun e G => G.trans (Φ e)) e
  exact ⟨G, fun _ => rfl, fun e U => hΦ e (G e U)⟩

/- English proof (translation)
Introduce `R _ I Y β hβ H m s _ hV`. Establish `hg` using `fun e => Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))`. Establish `hci : ∀ e, IsClosedImmersion (β e)` using `fun e =>`. Establish `: IsClosedImmersion (thickTrans R I e)` using `.spec_of_surjective _ (hg e)`. Use the proof step `MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hβ e).flip this`.

Establish `hsu : ∀ e, Surjective (β e)` using `fun e =>`. Establish `: Surjective (thickTrans R I e)` using `surjective_spec_of_nilpotent_ker _ (hg e) (isNilpotent_ker_factor I e)`. Use the proof step `MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip this`. Take `⟨G, hG0, hG⟩` from `exists_orderIso_opens_tower (fun e => (Y e).left) β`. Establish `hinj : ∀ e (U V : (Y (e + 1)).left.Opens), β e ⁻¹ᵁ U = β e ⁻¹ᵁ V → U = V`.

Introduce `e U V h`. Use extensionality with `x`. Take `⟨y, rfl⟩` from `(β e).surjective x`. Conclude with `Set.ext_iff.1 (congrArg (fun W : (Y e).left.Opens => (W : Set _)) h) y`. Use `⟨fun e S => G e (⨅ i ∈ S, nonzeroLocus (s i)), fun S => hG0 _, fun e S => hG e _, fun e S S' h => (G e).monotone (biInf_mono h), fun e S j => ?_, fun e => ?_, ?_⟩` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[← map_inf, Finset.iInf_insert, Finset.iInf_singleton, inf_comm]`. Use `beta_reduce`. Simplify using `only [Finset.iInf_singleton]`. Rewrite using `[← OrderIso.map_iSup, hV.1, OrderIso.map_top]`.

Introduce `e S hS beta_reduce`. Proceed by induction on `e with`. Consider the case `zero`. Rewrite using `[hG0]`. Conclude with `isAffineOpen_iInf_nonzeroLocus hV hS`.

Consider the case `succ e ih`. Take `⟨D, hD, he⟩` from `GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent _ _ _ (hg e) (isNilpotent_ker_factor I e) _ _ (Y (e + 1)).hom (Y e).hom (β e) (hβ e) _ ih`. Rewrite `hD` using `[hinj e _ _ (he.trans (hG e _).symm)]`. Then use the resulting hypothesis.
-/
theorem exists_basicOpens_of_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : LB (Y 0).left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy (Y 0).hom H s → ∃ D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens, (∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) ∧ (∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) ∧ (∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) ∧ (∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) ∧ (∀ e, ⨆ i, D e {i} = ⊤) ∧ (∀ e S, S.Nonempty → IsAffineOpen (D e S)) := by
  intro R _ I Y β hβ H m s _ hV
  have hg := fun e => Ideal.Quotient.factor_surjective
    (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))
  have hci : ∀ e, IsClosedImmersion (β e) := fun e =>
    have : IsClosedImmersion (thickTrans R I e) := .spec_of_surjective _ (hg e)
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hβ e).flip this
  have hsu : ∀ e, Surjective (β e) := fun e =>
    have : Surjective (thickTrans R I e) :=
      surjective_spec_of_nilpotent_ker _ (hg e) (isNilpotent_ker_factor I e)
    MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip this
  obtain ⟨G, hG0, hG⟩ := exists_orderIso_opens_tower (fun e => (Y e).left) β
  have hinj : ∀ e (U V : (Y (e + 1)).left.Opens), β e ⁻¹ᵁ U = β e ⁻¹ᵁ V → U = V := by
    intro e U V h
    ext x
    obtain ⟨y, rfl⟩ := (β e).surjective x
    exact Set.ext_iff.1 (congrArg (fun W : (Y e).left.Opens => (W : Set _)) h) y
  refine ⟨fun e S => G e (⨅ i ∈ S, nonzeroLocus (s i)), fun S => hG0 _, fun e S => hG e _,
    fun e S S' h => (G e).monotone (biInf_mono h), fun e S j => ?_, fun e => ?_, ?_⟩
  · beta_reduce
    rw [← map_inf, Finset.iInf_insert, Finset.iInf_singleton, inf_comm]
  · beta_reduce
    simp only [Finset.iInf_singleton]
    rw [← OrderIso.map_iSup, hV.1, OrderIso.map_top]
  · intro e S hS
    beta_reduce
    induction e with
    | zero =>
      rw [hG0]
      exact isAffineOpen_iInf_nonzeroLocus hV hS
    | succ e ih =>
      obtain ⟨D, hD, he⟩ := GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent
        _ _ _ (hg e) (isNilpotent_ker_factor I e) _ _ (Y (e + 1)).hom (Y e).hom (β e) (hβ e) _ ih
      rwa [hinj e _ _ (he.trans (hG e _).symm)] at hD

end GlobalTheory.CompanionTheory.FormalAlg.Lift
