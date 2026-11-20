import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PchainDNAlt

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

section Lin

variable {O : Type} [CommRing O] {A M : Type} [AddCommGroup A] [Module O A] [AddCommGroup M]
  [Module O M]

/- English proof (translation)
Use `choose g hg using hex`. Use `⟨{ toFun := fun a => K.mkQ (g a), map_add' := ?_, map_smul' := ?_ }, fun a => ⟨g a, hg a, rfl⟩⟩` and prove the remaining obligations. Introduce `a a'`. Rewrite using `[← map_add]`. Conclude with `(Submodule.Quotient.eq K).2 (huniq _ _ _ (hg (a + a')) (hadd _ _ _ _ (hg a) (hg a')))`.

Introduce `o a`. Rewrite using `[RingHom.id_apply, ← map_smul]`. Conclude with `(Submodule.Quotient.eq K).2 (huniq _ _ _ (hg (o • a)) (hsmul o _ _ (hg a)))`.
-/
theorem linLift (K : Submodule O M) (R : A → M → Prop) (hex : ∀ a, ∃ x, R a x)
    (hadd : ∀ a a' x x', R a x → R a' x' → R (a + a') (x + x'))
    (hsmul : ∀ (o : O) a x, R a x → R (o • a) (o • x))
    (huniq : ∀ a x x', R a x → R a x' → x - x' ∈ K) :
    ∃ ψ : A →ₗ[O] M ⧸ K, ∀ a, ∃ x, R a x ∧ ψ a = K.mkQ x := by
  choose g hg using hex
  refine ⟨{ toFun := fun a => K.mkQ (g a), map_add' := ?_, map_smul' := ?_ }, fun a => ⟨g a, hg a, rfl⟩⟩
  · intro a a'
    rw [← map_add]
    exact (Submodule.Quotient.eq K).2 (huniq _ _ _ (hg (a + a')) (hadd _ _ _ _ (hg a) (hg a')))
  · intro o a
    rw [RingHom.id_apply, ← map_smul]
    exact (Submodule.Quotient.eq K).2 (huniq _ _ _ (hg (o • a)) (hsmul o _ _ (hg a)))

end Lin

section bigCellDetWeightedEnergyIntegral

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

/- English proof (translation)
Use `set X := (Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hXdef`. Use `set Y := (Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hYdef`. Establish `hXY : X ≤ Y` using `Submodule.comap_mono le_sup_left`. Establish `hlen : Module.length O ((↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K) ⧸ Y.map K.mkQ) ≤ (L : ℕ∞)`. Rewrite using `[(Submodule.quotientQuotientEquivQuotientSup K Y).length_eq]`.

Use `le_trans ?_ hL` and prove the remaining obligations. Conclude with `Module.length_le_of_surjective (Submodule.mapQ Y (K ⊔ Y) LinearMap.id (fun y hy => Submodule.mem_sup_right (by simpa using hy))) (fun z => by`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Conclude with `⟨Submodule.Quotient.mk x, rfl⟩)`. Establish `h1` using `pstep_len (m := m) (c := cc) A ψ (Y.map K.mkQ) L kO hlen hkO hLc`.

Use `set A₁ := kerSub A ψ (Y.map K.mkQ) with hA₁def`. Establish `hA₁ : A₁ ≤ A` using `kerSub_le A ψ _`. Use `set ψ₁ : ↥A₁ →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K := ψ.comp (Submodule.inclusion hA₁)`. Use `set sN : Finset ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) := s.subtype (· ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)`. Use `set s' := sN.image K.mkQ`.

Establish `hcard : s'.card ≤ m`. Use `Finset.card_image_le.trans (le_trans ?_ hs)` and prove the remaining obligations. Rewrite using `[Finset.card_subtype]`. Conclude with `Finset.card_filter_le _ _`. Establish `hspan : Submodule.span O (↑s : Set (W.DD T)) = (Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i))).map (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype`.

Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Conclude with `⟨⟨y, hsN hy⟩, Finset.mem_subtype.2 hy, rfl⟩`. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `Finset.mem_subtype.1 hz`. Establish `hY : Y ≤ X ⊔ Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i))`. Introduce `z hz`.

Establish `hz' : (z : W.DD T) ∈ Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))` using `hz`. Take `⟨x, hx, t, ht, hxt⟩` from `Submodule.mem_sup.1 hz'`. Rewrite `ht` using `[hspan]`. Take `⟨t', ht', rfl⟩` from `Submodule.mem_map.1 ht`. Establish `hxN : x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i`.

Establish `e : x = (z : W.DD T) - (t' : W.DD T)` using `by rw [← hxt]; simp`. Rewrite using `[e]`. Conclude with `(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).sub_mem z.2 t'.2`. Use `Submodule.mem_sup.2 ⟨⟨x, hxN⟩, hx, t', ht', Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `using hxt`.

Establish `hgen : ∀ a, ψ₁ a ∈ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _)`. Introduce `a`. Establish `ha : ψ ⟨(a : FF), hA₁ a.2⟩ ∈ Y.map K.mkQ` using `(mem_kerSub_coe A ψ _ ⟨a, hA₁ a.2⟩).1 a.2`. Establish `hle : Y.map K.mkQ ≤ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Submodule.map_span, Finset.coe_image]`. Conclude with `hle ha`. Establish `h2` using `pstep_gen (lenO := lenOl PD (O := O)) (m := m) (c := cc) A₁ ψ₁ (X.map K.mkQ) s' hcard hgen`. Establish `heq : kerSub A₁ ψ₁ (X.map K.mkQ) = kerSub A ψ (X.map K.mkQ)`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨hx1, hx2⟩` from `(mem_kerSub A₁ ψ₁ _ x).1 hx`. Conclude with `(mem_kerSub A ψ _ x).2 ⟨hA₁ hx1, hx2⟩`. Introduce `hx`.

Take `⟨hx1, hx2⟩` from `(mem_kerSub A ψ _ x).1 hx`. Establish `hx1' : x ∈ A₁` using `(mem_kerSub A ψ _ x).2 ⟨hx1, Submodule.map_mono hXY hx2⟩`. Conclude with `(mem_kerSub A₁ ψ₁ _ x).2 ⟨hx1', hx2⟩`. Rewrite `h2` using `[heq]`. Conclude with `(pchain_of_len h1).trans (pchain_of_gen h2)`.
-/
theorem pchain_DN' (i : ZMod n) (k : ℕ) {m : ℕ} {cc : ℝ} {FF : Type} [AddCommGroup FF]
    [Module O FF] (K : Submodule O ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)) (s : Finset (W.DD T))
    (hs : s.card ≤ m) (hsN : (↑s : Set (W.DD T)) ⊆ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) (L kO : ℕ)
    (hL : Module.length O (↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸
      (Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))).comap
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype) ≤ (L : ℕ∞))
    (hkO : lenOl PD (O := O) = kO) (hLc : (L : ℝ) ≤ cc * kO) (A : Submodule O FF)
    (ψ : ↥A →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.PChain (lenOl PD (O := O)) m cc A
      (kerSub A ψ (((Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype).map K.mkQ)) 1 1 := by
  set X := (Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hXdef
  set Y := (Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))).comap
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hYdef
  have hXY : X ≤ Y := Submodule.comap_mono le_sup_left
  have hlen : Module.length O ((↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K) ⧸ Y.map K.mkQ) ≤ (L : ℕ∞) := by
    rw [(Submodule.quotientQuotientEquivQuotientSup K Y).length_eq]
    refine le_trans ?_ hL
    exact Module.length_le_of_surjective (Submodule.mapQ Y (K ⊔ Y) LinearMap.id
      (fun y hy => Submodule.mem_sup_right (by simpa using hy)))
      (fun z => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        exact ⟨Submodule.Quotient.mk x, rfl⟩)
  have h1 := pstep_len (m := m) (c := cc) A ψ (Y.map K.mkQ) L kO hlen hkO hLc
  set A₁ := kerSub A ψ (Y.map K.mkQ) with hA₁def
  have hA₁ : A₁ ≤ A := kerSub_le A ψ _
  set ψ₁ : ↥A₁ →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K := ψ.comp (Submodule.inclusion hA₁)
  set sN : Finset ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) := s.subtype (· ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)
  set s' := sN.image K.mkQ
  have hcard : s'.card ≤ m := by
    refine Finset.card_image_le.trans (le_trans ?_ hs)
    rw [Finset.card_subtype]
    exact Finset.card_filter_le _ _
  have hspan : Submodule.span O (↑s : Set (W.DD T)) =
      (Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i))).map
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype := by
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hsN hy⟩, Finset.mem_subtype.2 hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact Finset.mem_subtype.1 hz
  have hY : Y ≤ X ⊔ Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)) := by
    intro z hz
    have hz' : (z : W.DD T) ∈ Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T)) := hz
    obtain ⟨x, hx, t, ht, hxt⟩ := Submodule.mem_sup.1 hz'
    rw [hspan] at ht
    obtain ⟨t', ht', rfl⟩ := Submodule.mem_map.1 ht
    have hxN : x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i := by
      have e : x = (z : W.DD T) - (t' : W.DD T) := by rw [← hxt]; simp
      rw [e]; exact (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).sub_mem z.2 t'.2
    refine Submodule.mem_sup.2 ⟨⟨x, hxN⟩, hx, t', ht', Subtype.ext ?_⟩
    simpa using hxt
  have hgen : ∀ a, ψ₁ a ∈ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
    intro a
    have ha : ψ ⟨(a : FF), hA₁ a.2⟩ ∈ Y.map K.mkQ := (mem_kerSub_coe A ψ _ ⟨a, hA₁ a.2⟩).1 a.2
    have hle : Y.map K.mkQ ≤ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
      calc Y.map K.mkQ ≤ (X ⊔ Submodule.span O (↑sN : Set _)).map K.mkQ := Submodule.map_mono hY
        _ = X.map K.mkQ ⊔ (Submodule.span O (↑sN : Set _)).map K.mkQ := Submodule.map_sup _ _ _
        _ = X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
          rw [Submodule.map_span, Finset.coe_image]
    exact hle ha
  have h2 := pstep_gen (lenO := lenOl PD (O := O)) (m := m) (c := cc) A₁ ψ₁ (X.map K.mkQ) s' hcard hgen
  have heq : kerSub A₁ ψ₁ (X.map K.mkQ) = kerSub A ψ (X.map K.mkQ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := (mem_kerSub A₁ ψ₁ _ x).1 hx
      exact (mem_kerSub A ψ _ x).2 ⟨hA₁ hx1, hx2⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := (mem_kerSub A ψ _ x).1 hx
      have hx1' : x ∈ A₁ := (mem_kerSub A ψ _ x).2 ⟨hx1, Submodule.map_mono hXY hx2⟩
      exact (mem_kerSub A₁ ψ₁ _ x).2 ⟨hx1', hx2⟩
  rw [heq] at h2
  exact (pchain_of_len h1).trans (pchain_of_gen h2)

end bigCellDetWeightedEnergyIntegral

end Formalism.MainNotions.N.Pv.LocalLengthBound
