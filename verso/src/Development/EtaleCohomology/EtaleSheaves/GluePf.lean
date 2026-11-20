import Development.EtaleCohomology.EtaleSheaves.ProEqvPfA

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.ProEqvPf

namespace LateralTheory.E.GluePf

/- English proof (translation)
Establish `hb : (⊥ : Sieve X) ∈ Scheme.etaleTopology X` using `Scheme.bot_mem_grothendieckTopology X`. Establish `h1 : (𝟙 (F.obj.obj (op X))) = 0`. Apply `((F.cond (F.obj.obj (op X))) _ hb).isSeparatedFor.ext` to reduce the goal to its premises. Introduce `Y f hf`. Conclude with `hf.elim`.

Prove the components needed by the constructor for the conclusion. Introduce `a b`. Establish `ha : a = 0`. Use `congrArg (fun φ => (φ : F.obj.obj (op X) ⟶ _).hom a) h1` as an intermediate fact. Simplify using `using this`.

Establish `hb' : b = 0`. Use `congrArg (fun φ => (φ : F.obj.obj (op X) ⟶ _).hom b) h1` as an intermediate fact. Simplify using `using this`. Rewrite using `[ha, hb']`.
-/
theorem sec_sub {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) [IsEmpty X] : Subsingleton (Sec F X) := by
  have hb : (⊥ : Sieve X) ∈ Scheme.etaleTopology X := Scheme.bot_mem_grothendieckTopology X
  have h1 : (𝟙 (F.obj.obj (op X))) = 0 := by
    apply ((F.cond (F.obj.obj (op X))) _ hb).isSeparatedFor.ext
    intro Y f hf
    exact hf.elim
  constructor
  intro a b
  have ha : a = 0 := by
    have := congrArg (fun φ => (φ : F.obj.obj (op X) ⟶ _).hom a) h1
    simpa using this
  have hb' : b = 0 := by
    have := congrArg (fun φ => (φ : F.obj.obj (op X) ⟶ _).hom b) h1
    simpa using this
  rw [ha, hb']

/- English proof (translation)
Establish `e : hX.to Y ≫ f = 𝟙 X` using `hX.hom_ext _ _`. Establish `: x = pull R (sch.map (hX.to Y ≫ f)) F n x` using `by rw [e, CategoryTheory.Functor.map_id, pull_id]`. Rewrite using `[this, Functor.map_comp, pull_comp, hx, map_zero]`.
-/
theorem pull_inj_of_initial {R : Type} [CommRing R] {F : Shv R} {X Y : Scheme.{0}} (hX : IsInitial X) (f : Y ⟶ X) (n : ℤ)
    (x : H R (sch.obj X) F n) (hx : pull R (sch.map f) F n x = 0) : x = 0 := by
  have e : hX.to Y ≫ f = 𝟙 X := hX.hom_ext _ _
  have : x = pull R (sch.map (hX.to Y ≫ f)) F n x := by rw [e, CategoryTheory.Functor.map_id, pull_id]
  rw [this, Functor.map_comp, pull_comp, hx, map_zero]

/- English proof (translation)
Break down `lt_trichotomy n 0 with h | rfl | h` into its components or cases. Conclude with `(H.a9 (ZMod q) (tw q i)).1 _ n h`. Take `⟨e, -⟩` from `(H.a9 (ZMod q) (tw q i)).2`. Use `sec_sub (tw q i) X` as an intermediate fact. Conclude with `⟨fun a b => (e X).symm.injective (Subsingleton.elim _ _)⟩`.

Prove the components needed by the constructor for the conclusion. Establish `key : ∀ x : Ht q (sch.obj X) n i, x = 0`. Introduce `x`. Take `⟨Y, f, -, -, hf⟩` from `H.a5 (ZMod q) X (tw q i) n h x`. Conclude with `pull_inj_of_initial (isInitialOfIsEmpty) f n x hf`.

Introduce `a b`. Rewrite using `[key a, key b]`.
-/
theorem ht_sub (H : Hyp) (q : ℕ) (i n : ℤ) (X : Scheme.{0}) [IsEmpty X] : Subsingleton (Ht q (sch.obj X) n i) := by
  rcases lt_trichotomy n 0 with h | rfl | h
  · exact (H.a9 (ZMod q) (tw q i)).1 _ n h
  · obtain ⟨e, -⟩ := (H.a9 (ZMod q) (tw q i)).2
    have := sec_sub (tw q i) X
    exact ⟨fun a b => (e X).symm.injective (Subsingleton.elim _ _)⟩
  · constructor
    have key : ∀ x : Ht q (sch.obj X) n i, x = 0 := by
      intro x
      obtain ⟨Y, f, -, -, hf⟩ := H.a5 (ZMod q) X (tw q i) n h x
      exact pull_inj_of_initial (isInitialOfIsEmpty) f n x hf
    intro a b; rw [key a, key b]

def cmp {X : Scheme.{0}} (O : X.Opens) (hO : IsClosed (O : Set X)) : X.Opens := ⟨(O : Set X)ᶜ, hO.isOpen_compl⟩

/- English proof (translation)
Establish `: U.ι p ∈ Set.range U.ι` using `⟨p, rfl⟩`. Rewrite `this` using `[Scheme.Opens.range_ι]`. Then use the resulting hypothesis.
-/
theorem mem_ι {X : Scheme.{0}} (U : X.Opens) (p : U) : U.ι p ∈ U := by
  have : U.ι p ∈ Set.range U.ι := ⟨p, rfl⟩
  rwa [Scheme.Opens.range_ι] at this

/- English proof (translation)
Rewrite using `[← IsOpenImmersion.lift_fac u g hg, CategoryTheory.Functor.map_comp, pull_comp, hv, map_zero]`.
-/
theorem vanish_of_range {R : Type} [CommRing R] {F : Shv R} {X U Z : Scheme.{0}} (u : U ⟶ X) [IsOpenImmersion u] (g : Z ⟶ X)
    (hg : Set.range g ⊆ Set.range u) (n : ℤ) (v : H R (sch.obj X) F n) (hv : pull R (sch.map u) F n v = 0) :
    pull R (sch.map g) F n v = 0 := by
  rw [← IsOpenImmersion.lift_fac u g hg, CategoryTheory.Functor.map_comp, pull_comp, hv, map_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `p`. Establish `h` using `congrArg (fun φ => φ p) (pullback.condition (f := O1.ι) (g := O2.ι))`. Simplify using `only [Scheme.Hom.comp_apply] at h`. Establish `a` using `mem_ι O1 (pullback.fst O1.ι O2.ι p)`.

Establish `b` using `mem_ι O2 (pullback.snd O1.ι O2.ι p)`. Rewrite `b` using `[← h]`. Conclude with `hd _ a b`.
-/
theorem empty_pb' {X : Scheme.{0}} (O1 O2 : X.Opens) (hd : ∀ p, p ∈ O1 → p ∉ O2) :
    IsEmpty ((pullback O1.ι O2.ι : Scheme.{0})) := by
  constructor; intro p
  have h := congrArg (fun φ => φ p) (pullback.condition (f := O1.ι) (g := O2.ι))
  simp only [Scheme.Hom.comp_apply] at h
  have a := mem_ι O1 (pullback.fst O1.ι O2.ι p)
  have b := mem_ι O2 (pullback.snd O1.ι O2.ι p)
  rw [← h] at b
  exact hd _ a b

/- English proof (translation)
Rewrite using `[Scheme.Opens.range_ι, Scheme.Opens.range_ι]`. Use extensionality with `p`. Simplify using `only [Set.mem_union, Set.mem_univ, iff_true]`. Conclude with `hc p`.
-/
theorem cover' {X : Scheme.{0}} (O1 O2 : X.Opens) (hc : ∀ p, p ∈ O1 ∨ p ∈ O2) :
    Set.range O1.ι ∪ Set.range O2.ι = Set.univ := by
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  ext p; simp only [Set.mem_union, Set.mem_univ, iff_true]; exact hc p

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by ring⟩`. Take `⟨δ, hex, -⟩` from `hM H (ZMod q) (tw q i)`. Take `⟨w, rfl⟩` from `((hex O1.ι O2.ι (cover' O1 O2 hc) m).2.2 x).1 ⟨h1, h2⟩`. Use `empty_pb' O1 O2 hd` as an intermediate fact. Use `ht_sub H q i m (pullback O1.ι O2.ι)` as an intermediate fact.

Rewrite using `[Subsingleton.elim w 0, map_zero]`.
-/
theorem two_inj' (hM : MV) (H : Hyp) (q : ℕ) (i : ℤ) {X : Scheme.{0}} (O1 O2 : X.Opens) (hd : ∀ p, p ∈ O1 → p ∉ O2)
    (hc : ∀ p, p ∈ O1 ∨ p ∈ O2) (n : ℤ)
    (x : Ht q (sch.obj X) n i) (h1 : pull _ (sch.map O1.ι) _ _ x = 0) (h2 : pull _ (sch.map O2.ι) _ _ x = 0) : x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  obtain ⟨δ, hex, -⟩ := hM H (ZMod q) (tw q i)
  obtain ⟨w, rfl⟩ := ((hex O1.ι O2.ι (cover' O1 O2 hc) m).2.2 x).1 ⟨h1, h2⟩
  have := empty_pb' O1 O2 hd
  have := ht_sub H q i m (pullback O1.ι O2.ι)
  rw [Subsingleton.elim w 0, map_zero]

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `X O _ hc x _`. Establish `: IsEmpty X` using `⟨fun p => (hc p).elim fun j _ => j.elim0⟩`.

Use `ht_sub H q i n X` as an intermediate fact. Conclude with `Subsingleton.elim _ _`. Consider the case `succ k ih`. Introduce `X O hO hc x hx`. Set `A` to `O (Fin.last k)`.

Set `C` to `cmp A (hO _)`. Use `two_inj' hM H q i A C (fun p h1 h2 => h2 h1) (fun p => by by_cases h : p ∈ A; exacts [Or.inl h, Or.inr h]) n x (hx _) ?_` and prove the remaining obligations. Use `ih (fun j => C.ι ⁻¹ᵁ O j.castSucc) (fun j => (hO _).preimage C.ι.continuous) ?_ _ ?_` and prove the remaining obligations. Introduce `p`. Take `⟨j, hj⟩` from `hc (C.ι p)`.

Establish `hpc` using `mem_ι C p`. Consider the cases of `j using Fin.lastCases with`. Consider the case `last => exact absurd hj hpc`. Consider the case `cast j' => exact ⟨j', hj⟩`. Introduce `j`.

Rewrite using `[← pull_comp, ← CategoryTheory.Functor.map_comp]`. Use `vanish_of_range (O j.castSucc).ι _ ?_ n x (hx _)` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `mem_ι _ p`.
-/
theorem inj_fin (hM : MV) (H : Hyp) (q : ℕ) (i n : ℤ) : ∀ (k : ℕ) {X : Scheme.{0}} (O : Fin k → X.Opens),
    (∀ j, IsClosed (O j : Set X)) → (∀ p : X, ∃ j, p ∈ O j) → ∀ x : Ht q (sch.obj X) n i,
    (∀ j, pull _ (sch.map (O j).ι) _ _ x = 0) → x = 0 := by
  intro k
  induction k with
  | zero =>
    intro X O _ hc x _
    have : IsEmpty X := ⟨fun p => (hc p).elim fun j _ => j.elim0⟩
    have := ht_sub H q i n X
    exact Subsingleton.elim _ _
  | succ k ih =>
    intro X O hO hc x hx
    let A := O (Fin.last k)
    let C := cmp A (hO _)
    refine two_inj' hM H q i A C (fun p h1 h2 => h2 h1) (fun p => by by_cases h : p ∈ A; exacts [Or.inl h, Or.inr h]) n x
      (hx _) ?_
    refine ih (fun j => C.ι ⁻¹ᵁ O j.castSucc) (fun j => (hO _).preimage C.ι.continuous) ?_ _ ?_
    · intro p
      obtain ⟨j, hj⟩ := hc (C.ι p)
      have hpc := mem_ι C p
      cases j using Fin.lastCases with
      | last => exact absurd hj hpc
      | cast j' => exact ⟨j', hj⟩
    · intro j
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp]
      refine vanish_of_range (O j.castSucc).ι _ ?_ n x (hx _)
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact mem_ι _ p

/- English proof (translation)
Take `⟨δ, hex, -⟩` from `hM H (ZMod q) (tw q i)`. Use `empty_pb' O1 O2 hd` as an intermediate fact. Use `ht_sub H q i n (pullback O1.ι O2.ι)` as an intermediate fact. Conclude with `(hex O1.ι O2.ι (cover' O1 O2 hc) n).1 a b (Subsingleton.elim _ _)`.
-/
theorem two_glue' (hM : MV) (H : Hyp) (q : ℕ) (i : ℤ) {X : Scheme.{0}} (O1 O2 : X.Opens) (hd : ∀ p, p ∈ O1 → p ∉ O2)
    (hc : ∀ p, p ∈ O1 ∨ p ∈ O2) (n : ℤ) (a : Ht q (sch.obj O1) n i) (b : Ht q (sch.obj O2) n i) :
    ∃ x : Ht q (sch.obj X) n i, pull _ (sch.map O1.ι) _ _ x = a ∧ pull _ (sch.map O2.ι) _ _ x = b := by
  obtain ⟨δ, hex, -⟩ := hM H (ZMod q) (tw q i)
  have := empty_pb' O1 O2 hd
  have := ht_sub H q i n (pullback O1.ι O2.ι)
  exact (hex O1.ι O2.ι (cover' O1 O2 hc) n).1 a b (Subsingleton.elim _ _)

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro O _ _`. Conclude with `⟨0, fun j => j.elim0⟩`. Consider the case `succ k ih`.

Introduce `O hO hW`. Take `⟨x, hx⟩` from `ih (fun j => O j.castSucc) (fun j => hO _) (fun j => hW _)`. Set `A` to `O (Fin.last k)`. Set `C` to `cmp A (hO _)`. Take `⟨w, hw⟩` from `hW (Fin.last k)`.

Take `⟨x', h1, h2⟩` from `two_glue' hM H q i A C (fun p h1 h2 => h2 h1) (fun p => by by_cases h : p ∈ A; exacts [Or.inl h, Or.inr h]) n w (pull _ (sch.map C.ι) _ _ x)`. Establish `agreeA : pull _ (sch.map (φ ⁻¹ᵁ A).ι) _ _ (pull _ (sch.map φ) _ _ x') = pull _ (sch.map (φ ⁻¹ᵁ A).ι) _ _ z`. Rewrite using `[← pull_comp, ← CategoryTheory.Functor.map_comp, ← morphismRestrict_ι, CategoryTheory.Functor.map_comp, pull_comp, h1]`. Conclude with `hw`. Use `⟨x', fun j => ?_⟩` and prove the remaining obligations.

Consider the cases of `j using Fin.lastCases with`. Consider the case `last => exact agreeA`. Consider the case `cast j'`. Rewrite using `[← sub_eq_zero, ← map_sub]`. Set `V` to `φ ⁻¹ᵁ O j'.castSucc`.

Use `two_inj' hM H q i (V.ι ⁻¹ᵁ (φ ⁻¹ᵁ A)) (V.ι ⁻¹ᵁ (φ ⁻¹ᵁ C)) (fun p h1 h2 => h2 h1) (fun p => by by_cases h : p ∈ V.ι ⁻¹ᵁ (φ ⁻¹ᵁ A); exacts [Or.inl h, Or.inr h]) n _ ?_ ?_` and prove the remaining obligations. Rewrite using `[← pull_comp, ← CategoryTheory.Functor.map_comp]`. Use `vanish_of_range (φ ⁻¹ᵁ A).ι _ ?_ n _ (by rw [map_sub, agreeA, sub_self])` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Simplify using `only [Scheme.Hom.comp_apply]`. Conclude with `mem_ι _ p`. Establish `e : pull _ (sch.map φ) _ _ x' - z = pull _ (sch.map φ) _ _ (x' - x) + (pull _ (sch.map φ) _ _ x - z)`. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e, map_add, map_add, map_sub (pull _ (sch.map V.ι) _ _), hx j', sub_self, map_zero, add_zero, ← pull_comp, ← pull_comp, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]`. Use `vanish_of_range C.ι _ ?_ n _ (by rw [map_sub, h2, sub_self])` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Simplify using `only [Scheme.Hom.comp_apply]`.

Conclude with `mem_ι _ p`.
-/
theorem surj_fin (hM : MV) (H : Hyp) (q : ℕ) (i n : ℤ) {X P : Scheme.{0}} (φ : P ⟶ X) (z : Ht q (sch.obj P) n i) :
    ∀ (k : ℕ) (O : Fin k → X.Opens), (∀ j, IsClosed (O j : Set X)) →
    (∀ j, ∃ w : Ht q (sch.obj (O j)) n i, pull _ (sch.map (φ ∣_ O j)) _ _ w = pull _ (sch.map (φ ⁻¹ᵁ O j).ι) _ _ z) →
    ∃ x : Ht q (sch.obj X) n i, ∀ j, pull _ (sch.map (φ ⁻¹ᵁ O j).ι) _ _ (pull _ (sch.map φ) _ _ x) =
      pull _ (sch.map (φ ⁻¹ᵁ O j).ι) _ _ z := by
  intro k
  induction k with
  | zero => intro O _ _; exact ⟨0, fun j => j.elim0⟩
  | succ k ih =>
    intro O hO hW
    obtain ⟨x, hx⟩ := ih (fun j => O j.castSucc) (fun j => hO _) (fun j => hW _)
    let A := O (Fin.last k)
    let C := cmp A (hO _)
    obtain ⟨w, hw⟩ := hW (Fin.last k)
    obtain ⟨x', h1, h2⟩ := two_glue' hM H q i A C (fun p h1 h2 => h2 h1)
      (fun p => by by_cases h : p ∈ A; exacts [Or.inl h, Or.inr h]) n w (pull _ (sch.map C.ι) _ _ x)
    have agreeA : pull _ (sch.map (φ ⁻¹ᵁ A).ι) _ _ (pull _ (sch.map φ) _ _ x') = pull _ (sch.map (φ ⁻¹ᵁ A).ι) _ _ z := by
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp, ← morphismRestrict_ι, CategoryTheory.Functor.map_comp, pull_comp, h1]
      exact hw
    refine ⟨x', fun j => ?_⟩
    cases j using Fin.lastCases with
    | last => exact agreeA
    | cast j' =>
      rw [← sub_eq_zero, ← map_sub]
      let V := φ ⁻¹ᵁ O j'.castSucc
      refine two_inj' hM H q i (V.ι ⁻¹ᵁ (φ ⁻¹ᵁ A)) (V.ι ⁻¹ᵁ (φ ⁻¹ᵁ C)) (fun p h1 h2 => h2 h1)
        (fun p => by by_cases h : p ∈ V.ι ⁻¹ᵁ (φ ⁻¹ᵁ A); exacts [Or.inl h, Or.inr h]) n _ ?_ ?_
      · rw [← pull_comp, ← CategoryTheory.Functor.map_comp]
        refine vanish_of_range (φ ⁻¹ᵁ A).ι _ ?_ n _ (by rw [map_sub, agreeA, sub_self])
        rintro _ ⟨p, rfl⟩
        rw [Scheme.Opens.range_ι]
        simp only [Scheme.Hom.comp_apply]
        exact mem_ι _ p
      · have e : pull _ (sch.map φ) _ _ x' - z = pull _ (sch.map φ) _ _ (x' - x) + (pull _ (sch.map φ) _ _ x - z) := by
          rw [map_sub]; abel
        rw [e, map_add, map_add, map_sub (pull _ (sch.map V.ι) _ _), hx j', sub_self, map_zero, add_zero,
          ← pull_comp, ← pull_comp, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
        refine vanish_of_range C.ι _ ?_ n _ (by rw [map_sub, h2, sub_self])
        rintro _ ⟨p, rfl⟩
        rw [Scheme.Opens.range_ι]
        simp only [Scheme.Hom.comp_apply]
        exact mem_ι _ p

/- English proof (translation)
Take `⟨w, hw⟩` from `h`. Establish `hr : Set.range O.ι ⊆ Set.range u` using `by rw [Scheme.Opens.range_ι, hO]`. Set `r` to `IsOpenImmersion.lift u O.ι hr`. Establish `hr' : r ≫ u = O.ι` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hr'' : ∀ {Z : Scheme.{0}} (t : Y ⟶ Z), r ≫ u ≫ t = O.ι ≫ t`.

Introduce `Z t`. Rewrite using `[← Category.assoc, hr']`. Set `e : ((pullback.fst g (cpt A) ⁻¹ᵁ O : Scheme.{0})) ⟶ pullback (u ≫ g) (cpt A)` to `pullback.lift ((pullback.fst g (cpt A) ∣_ O) ≫ r) ((pullback.fst g (cpt A) ⁻¹ᵁ O).ι ≫ pullback.snd g (cpt A)) (by rw [Category.assoc, hr'', morphismRestrict_ι_assoc, pullback.condition, Category.assoc])`. Establish `he : e ≫ fm u g = (pullback.fst g (cpt A) ⁻¹ᵁ O).ι`. Unfold `fm`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [e, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hr', morphismRestrict_ι, pullback.map]`. Simplify using `only [e, Category.assoc, pullback.lift_snd, Category.comp_id, pullback.map]`. Use `⟨pull _ (sch.map r) _ _ w, ?_⟩` and prove the remaining obligations. Establish `h2 : (pullback.fst g (cpt A) ∣_ O) ≫ r = e ≫ pullback.fst (u ≫ g) (cpt A)` using `(pullback.lift_fst _ _ _).symm`.

Rewrite using `[← pull_comp, ← CategoryTheory.Functor.map_comp, h2, CategoryTheory.Functor.map_comp, pull_comp, hw, ← pull_comp, ← CategoryTheory.Functor.map_comp, he]`.
-/
theorem hit_opens (q : ℕ) (i n : ℤ) {A : Type} [CommRing A] [IsLocalRing A] {U Y : Scheme.{0}}
    (g : Y ⟶ Spec (CommRingCat.of A)) (z : Ht q (sch.obj (pullback g (cpt A))) n i) (u : U ⟶ Y) [IsOpenImmersion u]
    (O : Y.Opens) (hO : (O : Set Y) = Set.range u) (h : Hit q i n g z u) :
    ∃ w : Ht q (sch.obj O) n i, pull _ (sch.map (pullback.fst g (cpt A) ∣_ O)) _ _ w =
      pull _ (sch.map (pullback.fst g (cpt A) ⁻¹ᵁ O).ι) _ _ z := by
  obtain ⟨w, hw⟩ := h
  have hr : Set.range O.ι ⊆ Set.range u := by rw [Scheme.Opens.range_ι, hO]
  let r := IsOpenImmersion.lift u O.ι hr
  have hr' : r ≫ u = O.ι := IsOpenImmersion.lift_fac _ _ _
  have hr'' : ∀ {Z : Scheme.{0}} (t : Y ⟶ Z), r ≫ u ≫ t = O.ι ≫ t := by
    intro Z t; rw [← Category.assoc, hr']
  let e : ((pullback.fst g (cpt A) ⁻¹ᵁ O : Scheme.{0})) ⟶ pullback (u ≫ g) (cpt A) :=
    pullback.lift ((pullback.fst g (cpt A) ∣_ O) ≫ r) ((pullback.fst g (cpt A) ⁻¹ᵁ O).ι ≫ pullback.snd g (cpt A))
      (by rw [Category.assoc, hr'', morphismRestrict_ι_assoc, pullback.condition, Category.assoc])
  have he : e ≫ fm u g = (pullback.fst g (cpt A) ⁻¹ᵁ O).ι := by
    unfold fm
    apply pullback.hom_ext
    · simp only [e, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hr', morphismRestrict_ι, pullback.map]
    · simp only [e, Category.assoc, pullback.lift_snd, Category.comp_id, pullback.map]
  refine ⟨pull _ (sch.map r) _ _ w, ?_⟩
  have h2 : (pullback.fst g (cpt A) ∣_ O) ≫ r = e ≫ pullback.fst (u ≫ g) (cpt A) := (pullback.lift_fst _ _ _).symm
  rw [← pull_comp, ← CategoryTheory.Functor.map_comp, h2, CategoryTheory.Functor.map_comp, pull_comp, hw, ← pull_comp,
    ← CategoryTheory.Functor.map_comp, he]

/- English proof (translation)
Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun y => (O y : Set Y)) (fun y => (O y).isOpen) (fun p _ => Set.mem_iUnion.2 ⟨p, hO p⟩)`. Use `⟨t.card, fun j => (t.equivFin.symm j).1, fun p => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hp⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ p))`. Conclude with `⟨t.equivFin ⟨y, hy⟩, by simpa using hp⟩`.
-/
theorem fin_cover {Y : Scheme.{0}} [CompactSpace Y] (O : Y → Y.Opens) (hO : ∀ y, y ∈ O y) :
    ∃ (k : ℕ) (f : Fin k → Y), ∀ p, ∃ j, p ∈ O (f j) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (O y : Set Y)) (fun y => (O y).isOpen)
    (fun p _ => Set.mem_iUnion.2 ⟨p, hO p⟩)
  refine ⟨t.card, fun j => (t.equivFin.symm j).1, fun p => ?_⟩
  obtain ⟨y, hy, hp⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ p))
  exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hp⟩

def rg {U Y : Scheme.{0}} (u : U ⟶ Y) (h : IsOpenImmersion u) : Y.Opens := ⟨Set.range u, u.isOpenEmbedding.isOpen_range⟩

/- English proof (translation)
The claim follows from `u.isClosedEmbedding.isClosed_range`.
-/
theorem rg_closed {U Y : Scheme.{0}} (u : U ⟶ Y) (h : IsOpenImmersion u) (h' : IsClosedImmersion u) :
    IsClosed (rg u h : Set Y) := u.isClosedEmbedding.isClosed_range

/- English proof (translation)
Introduce `hM H q i A _ _ hq Y _ _ g n hI hS`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Use `choose U u hu using hI x hx`.

Take `⟨k, f, hf⟩` from `fin_cover (fun y => rg (u y) (hu y).1) (fun y => (hu y).2.2.1)`. Use `inj_fin hM H q i n k (fun j => rg (u (f j)) (hu (f j)).1) (fun j => rg_closed (u (f j)) (hu (f j)).1 (hu (f j)).2.1) hf x ?_` and prove the remaining obligations. Introduce `j`. Use `(hu (f j)).1` as an intermediate fact. Conclude with `vanish_of_range (u (f j)) _ (by rw [Scheme.Opens.range_ι]; exact fun _ h => h) n x (hu (f j)).2.2.2`.

Introduce `z choose U u hu using hS z`. Take `⟨k, f, hf⟩` from `fin_cover (fun y => rg (u y) (hu y).1) (fun y => (hu y).2.2.1)`. Take `⟨x, hx⟩` from `surj_fin hM H q i n (pullback.fst g (cpt A)) z k (fun j => rg (u (f j)) (hu (f j)).1) (fun j => rg_closed (u (f j)) (hu (f j)).1 (hu (f j)).2.1) (fun j => by have := (hu (f j)).1; exact hit_opens q i n g z (u (f j)) _ rfl (hu (f j)).2.2.2)`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`.

Use `inj_fin hM H q i n k (fun j => pullback.fst g (cpt A) ⁻¹ᵁ rg (u (f j)) (hu (f j)).1) (fun j => (rg_closed (u (f j)) (hu (f j)).1 (hu (f j)).2.1).preimage (pullback.fst g (cpt A)).continuous) (fun p => hf _) _ ?_` and prove the remaining obligations. Introduce `j`. Rewrite using `[map_sub, hx j, sub_self]`.
-/
theorem glue_of : Glue := by
  intro hM H q i A _ _ hq Y _ _ g n hI hS
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    choose U u hu using hI x hx
    obtain ⟨k, f, hf⟩ := fin_cover (fun y => rg (u y) (hu y).1) (fun y => (hu y).2.2.1)
    refine inj_fin hM H q i n k (fun j => rg (u (f j)) (hu (f j)).1) (fun j => rg_closed (u (f j)) (hu (f j)).1 (hu (f j)).2.1) hf x ?_
    intro j
    have := (hu (f j)).1
    exact vanish_of_range (u (f j)) _ (by rw [Scheme.Opens.range_ι]; exact fun _ h => h) n x (hu (f j)).2.2.2
  · intro z
    choose U u hu using hS z
    obtain ⟨k, f, hf⟩ := fin_cover (fun y => rg (u y) (hu y).1) (fun y => (hu y).2.2.1)
    obtain ⟨x, hx⟩ := surj_fin hM H q i n (pullback.fst g (cpt A)) z k (fun j => rg (u (f j)) (hu (f j)).1)
      (fun j => rg_closed (u (f j)) (hu (f j)).1 (hu (f j)).2.1)
      (fun j => by have := (hu (f j)).1; exact hit_opens q i n g z (u (f j)) _ rfl (hu (f j)).2.2.2)
    refine ⟨x, ?_⟩
    rw [← sub_eq_zero]
    refine inj_fin hM H q i n k (fun j => pullback.fst g (cpt A) ⁻¹ᵁ rg (u (f j)) (hu (f j)).1)
      (fun j => (rg_closed (u (f j)) (hu (f j)).1 (hu (f j)).2.1).preimage (pullback.fst g (cpt A)).continuous) (fun p => hf _) _ ?_
    intro j
    rw [map_sub, hx j, sub_self]

end LateralTheory.E.GluePf
