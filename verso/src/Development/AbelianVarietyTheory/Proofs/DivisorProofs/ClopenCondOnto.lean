import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev.Onto

/- English proof (translation)
Use `haveI : Unique (Sp k) := inferInstanceAs (Unique (PrimeSpectrum k))`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨default, h ⟨default, rfl⟩⟩`. Introduce and unpack `⟨t, ht⟩ _ ⟨t', rfl⟩`.

Rewrite using `[Subsingleton.elim t' t]` and apply the resulting hypothesis.
-/
theorem range_sp_subset_iff {k : Type} [Field k] {X : Scheme.{0}} (f : Sp k ⟶ X) (U : Set X) :
    Set.range f ⊆ U ↔ ∃ t, f t ∈ U := by
  haveI : Unique (Sp k) := inferInstanceAs (Unique (PrimeSpectrum k))
  constructor
  · intro h
    exact ⟨default, h ⟨default, rfl⟩⟩
  · rintro ⟨t, ht⟩ _ ⟨t', rfl⟩
    rwa [Subsingleton.elim t' t]

/- English proof (translation)
Use `haveI : Unique (Sp k) := inferInstanceAs (Unique (PrimeSpectrum k))`. Rewrite using `[range_sp_subset_iff, range_sp_subset_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht⟩ ⟨t', ht'⟩`. Rewrite `ht'` using `[Subsingleton.elim t' t]`.

Conclude with `ht ht'`. Introduce `h`. Conclude with `⟨default, fun h' => h ⟨default, h'⟩⟩`.
-/
theorem range_sp_subset_compl {k : Type} [Field k] {X : Scheme.{0}} (f : Sp k ⟶ X) (U : Set X) :
    Set.range f ⊆ Uᶜ ↔ ¬ Set.range f ⊆ U := by
  haveI : Unique (Sp k) := inferInstanceAs (Unique (PrimeSpectrum k))
  rw [range_sp_subset_iff, range_sp_subset_iff]
  constructor
  · rintro ⟨t, ht⟩ ⟨t', ht'⟩
    rw [Subsingleton.elim t' t] at ht'
    exact ht ht'
  · intro h
    exact ⟨default, fun h' => h ⟨default, h'⟩⟩

end GlobalTheory.UPel.HT.EtLev.Onto

namespace GlobalTheory.UPel.HT.EtLev

open GlobalTheory.UPel.HT.EtLev.Onto

/- English proof (translation)
Introduce `p _ D R _ b N w0 r hw S _ s o K κ hKf hKe hκ hrep Z et hZf hZe hadd hlin hker`. Use `haveI := hKf`. Use `haveI := hKe`. Use `haveI := hZf`. Use `haveI := hZe`.

Establish `hkc : ∀ (T T' : Over S) (f : T ⟶ T') (g : T' ⟶ o.A), (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∀ c ∈ w0 ^ r, (f ≫ g) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1`. Introduce `T T' f g hg c hc`. Rewrite using `[Category.assoc, hg c hc, MonObj.comp_one]`. Establish `hetk : ∀ a, ∀ c ∈ w0 ^ r, et a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1` using `fun a c hc => by`. Rewrite using `[← hlin]`.

Conclude with `hker _ (Submodule.subset_span ⟨c, hc, a, rfl⟩)`. Establish `huniq : ∀ (T : Over S) (y y' : T ⟶ K), y ≫ κ = y' ≫ κ → y = y'` using `fun T y y' h => (hrep T (y' ≫ κ) (hkc _ _ y' κ hκ)).unique h rfl`. Use `choose lam hlam using fun a => (hrep Z (et a) (hetk a)).exists`. Use `haveI := D.freeLa`. Use `haveI := D.finLa`.

Take `⟨J, _, q, hq⟩` from `LevCover.exists_finite_mod D.La (pow_pos (Fact.out : p.Prime).pos r)`. Establish `hlamq : ∀ a a', q a = q a' → lam a = lam a'`. Introduce `a a' h`. Take `⟨c, rfl⟩` from `hq a a' h`. Establish `hm : p ^ r • c ∈ wSub D w0 r`.

Use `Submodule.subset_span ⟨(p : 𝓞 D.F) ^ r, Ideal.pow_mem_pow hw.2.1 r, c, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`. Apply `huniq` to reduce the goal to its premises. Rewrite using `[hlam, hlam, hadd, hker _ hm, _root_.mul_one]`. Establish `hfin : (Set.range lam).Finite`.

Use `(Set.finite_range fun j : Set.range q => lam j.2.choose).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Use `⟨⟨q a, Set.mem_range_self a⟩, ?_⟩` and prove the remaining obligations. Conclude with `hlamq _ _ (Classical.choose_spec (Set.mem_range_self (f := q) a))`. Take `⟨hPf, hPe⟩` from `LevCover.finiteEtale_tensor Z K`.

Use `haveI := hPf`. Use `haveI := hPe`. Set `U : (Z ⟶ K) → (Z ⊗ K).left.Opens` to `fun l => (LevCover.clopenCond_eq (snd Z K) (fst Z K ≫ l)).choose`. Establish `hU : ∀ l, IsClosed (U l : Set (Z ⊗ K).left) ∧ ∀ (T' : Over S) (h : T' ⟶ Z ⊗ K), h ≫ snd Z K = h ≫ fst Z K ≫ l ↔ Set.range h.left ⊆ U l` using `fun l => (LevCover.clopenCond_eq (snd Z K) (fst Z K ≫ l)).choose_spec`. Set `C : Set (Z ⊗ K).left` to `⋂ l ∈ Set.range lam, (U l : Set (Z ⊗ K).left)ᶜ`.

Establish `hCo : IsOpen C` using `hfin.isOpen_biInter fun l _ => (hU l).1.isOpen_compl`. Establish `hCc : IsClosed C` using `isClosed_biInter fun l _ => (U l).isOpen.isClosed_compl`. Take `⟨V, i, hVf, hVe, -, hV⟩` from `LevCover.exists_sub (Z := Z ⊗ K) ⟨C, hCo⟩ hCc`. Use `haveI := hVf`. Use `haveI := hVe`.

Take `⟨I, hIc, hI⟩` from `LevCover.exists_image (i ≫ fst Z K)`. Establish `hA : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ Z), Set.range z.left ⊆ (I : Set Z.left)ᶜ ↔ ∀ g : Over.mk x ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃ a, z ≫ et a = g`. Introduce `k _ _ x z`. Rewrite using `[range_sp_subset_compl, hI k x z]`. Prove the components needed by the constructor for the conclusion.

Introduce `hno g hg`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨y, hy, -⟩` from `hrep _ g hg`. Apply `hno` to reduce the goal to its premises.

Establish `hmem : Set.range (lift z y).left ⊆ C`. Use `Set.subset_iInter₂ fun l hl => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `hl`. Rewrite using `[range_sp_subset_compl, ← (hU _).2]`. Introduce `h`.

Simplify using `only [lift_snd, lift_fst_assoc] at h`. Apply `hne a` to reduce the goal to its premises. Rewrite using `[← hy, h, Category.assoc, hlam]`. Take `⟨w, hw⟩` from `(hV _ (lift z y)).1 hmem`. Conclude with `⟨w, by rw [← Category.assoc, hw, lift_fst]⟩`.

Introduce and unpack `hall ⟨w, hw⟩`. Take `⟨a, ha⟩` from `hall ((w ≫ i) ≫ snd Z K ≫ κ) (hkc _ _ _ _ (hkc _ _ _ _ hκ))`. Establish `hs : (w ≫ i) ≫ snd Z K = (w ≫ i) ≫ fst Z K ≫ lam a`. Apply `huniq` to reduce the goal to its premises. Use `ha` as an intermediate fact.

Rewrite `this` using `[← hw]`. Simplify `this.symm` using `only [Category.assoc, hlam]`. Establish `h1` using `((hU (lam a)).2 _ _).1 hs`. Establish `h2 : Set.range (w ≫ i).left ⊆ C` using `(hV _ _).2 ⟨w, rfl⟩`. Use `haveI : Unique (Over.mk x).left := inferInstanceAs (Unique (PrimeSpectrum k))`.

Establish `h3` using `h2 ⟨default, rfl⟩`. Conclude with `Set.mem_iInter₂.1 h3 (lam a) ⟨a, rfl⟩ (h1 ⟨default, rfl⟩)`. Use `⟨⟨(I : Set Z.left)ᶜ, hIc.isOpen_compl⟩, I.isOpen.isClosed_compl, fun T' h => ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `H`.

Apply `LevCover.range_subset_of_geom h` to reduce the goal to its premises. Introduce `k _ _ x y`. Establish `e : (y ≫ h).left = ((Over.homMk y.left rfl : Over.mk (y.left ≫ T'.hom) ⟶ T') ≫ h).left` using `rfl`. Rewrite using `[e]`. Express the relevant statement in the definitionally equal form `_ ⊆ (I : Set Z.left)ᶜ`.

Rewrite using `[hA]`. Introduce `g hg`. Take `⟨a, ha⟩` from `H k y.left g hg`. Conclude with `⟨a, by rw [Category.assoc]; exact ha⟩`. Introduce `H k _ _ xp g hg`.

Establish `hsub : Set.range ((Over.homMk xp rfl : Over.mk (xp ≫ T'.hom) ⟶ T') ≫ h).left ⊆ (I : Set Z.left)ᶜ`. Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `H ⟨xp t, by simp⟩`. Take `⟨a, ha⟩` from `(hA k (xp ≫ T'.hom) _).1 hsub g hg`. Conclude with `⟨a, by rw [← Category.assoc]; exact ha⟩`.
-/
theorem clopenCond_onto : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), ∀ g : Over.mk (x ≫ T'.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = g := by
  intro p _ D R _ b N w0 r hw S _ s o K κ hKf hKe hκ hrep Z et hZf hZe hadd hlin hker
  haveI := hKf; haveI := hKe; haveI := hZf; haveI := hZe
  have hkc : ∀ (T T' : Over S) (f : T ⟶ T') (g : T' ⟶ o.A),
      (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
      ∀ c ∈ w0 ^ r, (f ≫ g) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T T' f g hg c hc
    rw [Category.assoc, hg c hc, MonObj.comp_one]
  have hetk : ∀ a, ∀ c ∈ w0 ^ r, et a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun a c hc => by
    rw [← hlin]
    exact hker _ (Submodule.subset_span ⟨c, hc, a, rfl⟩)
  have huniq : ∀ (T : Over S) (y y' : T ⟶ K), y ≫ κ = y' ≫ κ → y = y' := fun T y y' h =>
    (hrep T (y' ≫ κ) (hkc _ _ y' κ hκ)).unique h rfl
  choose lam hlam using fun a => (hrep Z (et a) (hetk a)).exists
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨J, _, q, hq⟩ := LevCover.exists_finite_mod D.La (pow_pos (Fact.out : p.Prime).pos r)
  have hlamq : ∀ a a', q a = q a' → lam a = lam a' := by
    intro a a' h
    obtain ⟨c, rfl⟩ := hq a a' h
    have hm : p ^ r • c ∈ wSub D w0 r := by
      refine Submodule.subset_span ⟨(p : 𝓞 D.F) ^ r, Ideal.pow_mem_pow hw.2.1 r, c, ?_⟩
      rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    apply huniq
    rw [hlam, hlam, hadd, hker _ hm, _root_.mul_one]
  have hfin : (Set.range lam).Finite := by
    refine (Set.finite_range fun j : Set.range q => lam j.2.choose).subset ?_
    rintro _ ⟨a, rfl⟩
    refine ⟨⟨q a, Set.mem_range_self a⟩, ?_⟩
    exact hlamq _ _ (Classical.choose_spec (Set.mem_range_self (f := q) a))
  obtain ⟨hPf, hPe⟩ := LevCover.finiteEtale_tensor Z K
  haveI := hPf; haveI := hPe
  let U : (Z ⟶ K) → (Z ⊗ K).left.Opens := fun l => (LevCover.clopenCond_eq (snd Z K) (fst Z K ≫ l)).choose
  have hU : ∀ l, IsClosed (U l : Set (Z ⊗ K).left) ∧ ∀ (T' : Over S) (h : T' ⟶ Z ⊗ K),
      h ≫ snd Z K = h ≫ fst Z K ≫ l ↔ Set.range h.left ⊆ U l := fun l =>
    (LevCover.clopenCond_eq (snd Z K) (fst Z K ≫ l)).choose_spec
  let C : Set (Z ⊗ K).left := ⋂ l ∈ Set.range lam, (U l : Set (Z ⊗ K).left)ᶜ
  have hCo : IsOpen C := hfin.isOpen_biInter fun l _ => (hU l).1.isOpen_compl
  have hCc : IsClosed C := isClosed_biInter fun l _ => (U l).isOpen.isClosed_compl
  obtain ⟨V, i, hVf, hVe, -, hV⟩ := LevCover.exists_sub (Z := Z ⊗ K) ⟨C, hCo⟩ hCc
  haveI := hVf; haveI := hVe
  obtain ⟨I, hIc, hI⟩ := LevCover.exists_image (i ≫ fst Z K)
  have hA : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ Z),
      Set.range z.left ⊆ (I : Set Z.left)ᶜ ↔ ∀ g : Over.mk x ⟶ o.A,
        (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃ a, z ≫ et a = g := by
    intro k _ _ x z
    rw [range_sp_subset_compl, hI k x z]
    constructor
    · intro hno g hg
      by_contra hne
      push_neg at hne
      obtain ⟨y, hy, -⟩ := hrep _ g hg
      apply hno
      have hmem : Set.range (lift z y).left ⊆ C := by
        refine Set.subset_iInter₂ fun l hl => ?_
        obtain ⟨a, rfl⟩ := hl
        rw [range_sp_subset_compl, ← (hU _).2]
        intro h
        simp only [lift_snd, lift_fst_assoc] at h
        apply hne a
        rw [← hy, h, Category.assoc, hlam]
      obtain ⟨w, hw⟩ := (hV _ (lift z y)).1 hmem
      exact ⟨w, by rw [← Category.assoc, hw, lift_fst]⟩
    · rintro hall ⟨w, hw⟩
      obtain ⟨a, ha⟩ := hall ((w ≫ i) ≫ snd Z K ≫ κ) (hkc _ _ _ _ (hkc _ _ _ _ hκ))
      have hs : (w ≫ i) ≫ snd Z K = (w ≫ i) ≫ fst Z K ≫ lam a := by
        apply huniq
        have := ha
        rw [← hw] at this
        simpa only [Category.assoc, hlam] using this.symm
      have h1 := ((hU (lam a)).2 _ _).1 hs
      have h2 : Set.range (w ≫ i).left ⊆ C := (hV _ _).2 ⟨w, rfl⟩
      haveI : Unique (Over.mk x).left := inferInstanceAs (Unique (PrimeSpectrum k))
      have h3 := h2 ⟨default, rfl⟩
      exact Set.mem_iInter₂.1 h3 (lam a) ⟨a, rfl⟩ (h1 ⟨default, rfl⟩)
  refine ⟨⟨(I : Set Z.left)ᶜ, hIc.isOpen_compl⟩, I.isOpen.isClosed_compl, fun T' h => ?_⟩
  constructor
  · intro H
    apply LevCover.range_subset_of_geom h
    intro k _ _ x y
    have e : (y ≫ h).left = ((Over.homMk y.left rfl : Over.mk (y.left ≫ T'.hom) ⟶ T') ≫ h).left := rfl
    rw [e]
    change _ ⊆ (I : Set Z.left)ᶜ
    rw [hA]
    intro g hg
    obtain ⟨a, ha⟩ := H k y.left g hg
    exact ⟨a, by rw [Category.assoc]; exact ha⟩
  · intro H k _ _ xp g hg
    have hsub : Set.range ((Over.homMk xp rfl : Over.mk (xp ≫ T'.hom) ⟶ T') ≫ h).left ⊆ (I : Set Z.left)ᶜ := by
      rintro _ ⟨t, rfl⟩
      exact H ⟨xp t, by simp⟩
    obtain ⟨a, ha⟩ := (hA k (xp ≫ T'.hom) _).1 hsub g hg
    exact ⟨a, by rw [← Category.assoc]; exact ha⟩

end GlobalTheory.UPel.HT.EtLev
