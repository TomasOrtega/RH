import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.KummerTheory

/- English proof (translation)
Establish `: Subsingleton (Ht q (sch.obj (pullback p (Spec.map s))) n i)` using `(h9 (ZMod q) (tw q i)).1 _ n hn`. Use `haveI : ∀ a : Fin (M + 1), Subsingleton (Ht q (sch.obj (Spec A)) (n - ((a : ℕ) : ℤ)) 0) := fun a => (h9 (ZMod q) (tw q 0)).1 _ _ (by omega)`. Use `⟨fun y _ => ?_, fun b => ⟨0, Subsingleton.elim _ _⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a t`. Conclude with `Subsingleton.elim _ _`.
-/
theorem stalk_neg (h9 : A9) (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
    (A : CommRingCat.{0}) (s : R ⟶ A) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ)
    (n : ℤ) (hn : n < 0) : IsoUpTo N (lh q p (Spec.map s) i r c M n) := by
  have : Subsingleton (Ht q (sch.obj (pullback p (Spec.map s))) n i) := (h9 (ZMod q) (tw q i)).1 _ n hn
  haveI : ∀ a : Fin (M + 1), Subsingleton (Ht q (sch.obj (Spec A)) (n - ((a : ℕ) : ℤ)) 0) :=
    fun a => (h9 (ZMod q) (tw q 0)).1 _ _ (by omega)
  refine ⟨fun y _ => ?_, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  funext a t
  exact Subsingleton.elim _ _

def ExtOne : Prop := DivisorNaturality → DivisorRingCompatibility → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R A : CommRingCat.{0}} (p : X ⟶ Spec R)
  (s : R ⟶ A), IsUnit (q : A) → ∀ (a i : ℤ) (x : Ht q (sch.obj X) a i) (t : ZMod q),
    ext q p (Spec.map s) a a i x ((t • one q (sch.obj (Spec A))).cast (by ring) rfl) =
      t • pull _ (sch.map (pullback.fst p (Spec.map s))) _ _ x

def StalkTop : Prop := DivisorNaturality → DivisorRingCompatibility → A9 → B2 → H0 → ExtOne → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}}
  {R : CommRingCat.{0}} (p : X ⟶ Spec R) (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsUnit (q : R) → ∀ (i : ℤ) (r : ℕ → ℕ)
  (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ), Eqv _ (sch.map (pullback.fst p (Spec.map s))) (tw q i) →
  (∀ a ≤ M, IsoUpTo N (comb q (c a))) → ∀ n : ℤ, 0 ≤ n → n ≤ M → IsoUpTo N (lh q p (Spec.map s) i r c M n)

/- English proof (translation)
Introduce `U ⟨g⟩`. Establish `g' : U ⟶ X` using `g`. Simplify using `using hq.map g'.appTop.hom`.
-/
theorem inv_sch (q : ℕ) {X : Scheme.{0}} (hq : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  intro U ⟨g⟩
  have g' : U ⟶ X := g
  simpa using hq.map g'.appTop.hom

/- English proof (translation)
Simplify using `using hq.map (Scheme.ΓSpecIso A).inv.hom`.
-/
theorem unit_spec (q : ℕ) {A : CommRingCat.{0}} (hq : IsUnit (q : A)) : IsUnit (q : Γ(Spec A, ⊤)) := by
  simpa using hq.map (Scheme.ΓSpecIso A).inv.hom

/- English proof (translation)
Rewrite using `[← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]`.
-/
theorem pull_zsmul {E E' : Spc} (f : E ⟶ E') (q : ℕ) [NeZero q] {n i : ℤ} (t : ZMod q) (x : Ht q E' n i) :
    pull _ f _ _ (t • x) = t • pull _ f _ _ x := by
  rw [← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

/- English proof (translation)
Substitute `h1 h2 h3 h4` using the available equality. Both sides reduce to the same expression.
-/
theorem cast_cast' (q : ℕ) {E : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'')
    (x : Ht q E n i) : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

/- English proof (translation)
Substitute `h1 h2` using the available equality. Both sides reduce to the same expression.
-/
theorem pull_cast (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (x.cast h1 h2) = Ht.cast h1 h2 (pull _ f _ _ x : Ht q E n i) := by
  subst h1 h2; rfl

/- English proof (translation)
Substitute `h1 h2` using the available equality. Both sides reduce to the same expression.
-/
theorem cast_smul' (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (t : ZMod q) (x : Ht q E n i) :
    (t • x).cast h1 h2 = t • x.cast h1 h2 := by
  subst h1 h2; rfl

/- English proof (translation)
Substitute `h1 h2` using the available equality. Both sides reduce to the same expression.
-/
theorem cup_cast_r (q : ℕ) {E : Spc} {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i)
    (y : Ht q E m j) : cup q a (y.cast h1 h2) = (cup q a y).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

/- English proof (translation)
Rewrite using `[← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]`.
-/
theorem cup_smul_r (q : ℕ) [NeZero q] {E : Spc} {n m i j : ℤ} (t : ZMod q) (a : Ht q E n i) (y : Ht q E m j) :
    cup q a (t • y) = t • cup q a y := by
  rw [← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

/- English proof (translation)
Simplify using `using hq.map f.appTop.hom`.
-/
theorem unit_map (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) (hq : IsUnit (q : Γ(X, ⊤))) : IsUnit (q : Γ(Y, ⊤)) := by
  simpa using hq.map f.appTop.hom

/- English proof (translation)
Introduce `h6n h6r q _ X R A p s hq a i x t`. Establish `hI` using `inv_sch q (unit_spec q hq)`. Establish `hP` using `inv_sch q (unit_map q (pullback.snd p (Spec.map s)) (unit_spec q hq))`. Unfold `ext`. Rewrite using `[pull_cast, pull_zsmul, (h6n q).2.1 _ hI, cup_cast_r, cup_smul_r, (h6r q _).2.2, (h6r q _).1 hP]`.

Simplify using `only [mul_zero, Int.negOnePow_zero, one_smul, cast_smul', cast_cast']`. Both sides reduce to the same expression.
-/
theorem extOne_pf : ExtOne := by
  intro h6n h6r q _ X R A p s hq a i x t
  have hI := inv_sch q (unit_spec q hq)
  have hP := inv_sch q (unit_map q (pullback.snd p (Spec.map s)) (unit_spec q hq))
  unfold ext
  rw [pull_cast, pull_zsmul, (h6n q).2.1 _ hI, cup_cast_r, cup_smul_r, (h6r q _).2.2, (h6r q _).1 hP]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, cast_smul', cast_cast']
  rfl

/- English proof (translation)
Substitute `h1 h2` using the available equality. Both sides reduce to the same expression.
-/
theorem cast_zero' (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    (0 : Ht q E n i).cast h1 h2 = 0 := by
  subst h1 h2; rfl

/- English proof (translation)
Substitute `h1 h2` using the available equality. Both sides reduce to the same expression.
-/
theorem cast_nsmul' (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (N : ℕ) (x : Ht q E n i) :
    (N • x).cast h1 h2 = N • x.cast h1 h2 := by
  subst h1 h2; rfl

/- English proof (translation)
Unfold `ext`. Rewrite using `[map_zero, map_zero, cast_zero']`.
-/
theorem ext_zero (q : ℕ) [NeZero q] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i) :
    ext q pX pY a n i x 0 = 0 := by
  unfold ext; rw [map_zero, map_zero, cast_zero']

/- English proof (translation)
Introduce `h6n h6r h9 hb2 h0 hE q _ X R p A s hA hq i r c M N he hc n hn0 hnM`. Use `lift n to ℕ using hn0`. Establish `hnM' : n ≤ M` using `by exact_mod_cast hnM`. Establish `hqA : IsUnit (q : A)` using `by simpa using hq.map s.hom`. Set `a : Fin (M + 1)` to `⟨n, by omega⟩`.

Establish `hsub : ∀ b : Fin (M + 1), b ≠ a → Subsingleton (Ht q (sch.obj (Spec A)) ((n : ℤ) - ((b : ℕ) : ℤ)) 0)`. Introduce `b hb`. Establish `hb' : (b : ℕ) ≠ n` using `fun h => hb (Fin.ext h)`. Break down `Nat.lt_or_gt_of_ne hb' with h | h` into its components or cases. Conclude with `hb2 (ZMod q) A hA (tw q 0) _ (by omega)`.

Conclude with `(h9 (ZMod q) (tw q 0)).1 _ _ (by omega)`. Establish `hH` using `h0 h9 q A hA hqA`. Establish `hex : ∀ z : Ht q (sch.obj (Spec A)) ((n : ℤ) - (n : ℤ)) 0, ∃ t : ZMod q, z = (t • one q (sch.obj (Spec A))).cast (by ring) rfl`. Introduce `z`. Take `⟨t, ht⟩` from `hH.2 (z.cast (by ring) rfl)`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[show t • one q (sch.obj (Spec A)) = _ from ht, cast_cast']`. Both sides reduce to the same expression. Establish `hform : ∀ (y : ∀ b : Fin (M + 1), Fin (r b) → Ht q (sch.obj (Spec A)) ((n : ℤ) - ((b : ℕ) : ℤ)) 0) (t : Fin (r n) → ZMod q), (∀ u, y a u = (t u • one q (sch.obj (Spec A))).cast (by ring) rfl) → lh q p (Spec.map s) i r c M n y = pull _ (sch.map (pullback.fst p (Spec.map s))) _ _ ( …`. Introduce `y t hy`.

Unfold `lh comb`. Rewrite using `[Fintype.sum_eq_single a]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[hy u, pull_zsmul]`.

Conclude with `hE h6n h6r q p s hqA n i (c n u) (t u)`. Introduce `b hb haveI := hsub b hb`. Use `Finset.sum_eq_zero fun u _ => ?_` and prove the remaining obligations. Rewrite using `[Subsingleton.elim (y b u) 0, ext_zero]`. Establish `hbij` using `he (n : ℤ)`.

Use `⟨fun y hy0 => ?_, fun b => ?_⟩` and prove the remaining obligations. Use `choose t ht using fun u => hex (y a u)`. Rewrite `hy0` using `[hform y t ht]`. Establish `hc0 : comb q (c n) t = 0` using `hbij.1 (by rw [hy0, map_zero])`. Establish `hNt` using `(hc n hnM').1 t hc0`.

Use function extensionality and compare the values at `b u`. Distinguish the cases in `hb : b = a`. Substitute `hb show N • y a u = 0` using the available equality. Rewrite using `[ht u]`. Establish `e1 : N • t u = 0` using `by simpa using congrFun hNt u`.

Rewrite using `[← cast_nsmul', ← smul_assoc, e1, zero_smul, cast_zero']`. Use `haveI := hsub b hb`. Conclude with `Subsingleton.elim _ _`. Take `⟨w, rfl⟩` from `hbij.2 b`. Take `⟨t, ht⟩` from `(hc n hnM').2 w`.

Use `⟨Pi.single a (fun u => (t u • one q (sch.obj (Spec A))).cast (by ring) rfl), ?_⟩` and prove the remaining obligations. Rewrite using `[hform _ t (fun u => by rw [Pi.single_eq_same]), ht, map_nsmul]`.
-/
theorem stalkTop_pf : StalkTop := by
  intro h6n h6r h9 hb2 h0 hE q _ X R p A s hA hq i r c M N he hc n hn0 hnM
  lift n to ℕ using hn0
  have hnM' : n ≤ M := by exact_mod_cast hnM
  have hqA : IsUnit (q : A) := by simpa using hq.map s.hom
  let a : Fin (M + 1) := ⟨n, by omega⟩
  have hsub : ∀ b : Fin (M + 1), b ≠ a → Subsingleton (Ht q (sch.obj (Spec A)) ((n : ℤ) - ((b : ℕ) : ℤ)) 0) := by
    intro b hb
    have hb' : (b : ℕ) ≠ n := fun h => hb (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hb' with h | h
    · exact hb2 (ZMod q) A hA (tw q 0) _ (by omega)
    · exact (h9 (ZMod q) (tw q 0)).1 _ _ (by omega)
  have hH := h0 h9 q A hA hqA
  have hex : ∀ z : Ht q (sch.obj (Spec A)) ((n : ℤ) - (n : ℤ)) 0, ∃ t : ZMod q,
      z = (t • one q (sch.obj (Spec A))).cast (by ring) rfl := by
    intro z
    obtain ⟨t, ht⟩ := hH.2 (z.cast (by ring) rfl)
    refine ⟨t, ?_⟩
    rw [show t • one q (sch.obj (Spec A)) = _ from ht, cast_cast']; rfl
  have hform : ∀ (y : ∀ b : Fin (M + 1), Fin (r b) → Ht q (sch.obj (Spec A)) ((n : ℤ) - ((b : ℕ) : ℤ)) 0)
      (t : Fin (r n) → ZMod q), (∀ u, y a u = (t u • one q (sch.obj (Spec A))).cast (by ring) rfl) →
      lh q p (Spec.map s) i r c M n y = pull _ (sch.map (pullback.fst p (Spec.map s))) _ _ (comb q (c n) t) := by
    intro y t hy
    unfold lh comb
    rw [Fintype.sum_eq_single a]
    · rw [map_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hy u, pull_zsmul]
      exact hE h6n h6r q p s hqA n i (c n u) (t u)
    · intro b hb
      haveI := hsub b hb
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [Subsingleton.elim (y b u) 0, ext_zero]
  have hbij := he (n : ℤ)
  refine ⟨fun y hy0 => ?_, fun b => ?_⟩
  · choose t ht using fun u => hex (y a u)
    rw [hform y t ht] at hy0
    have hc0 : comb q (c n) t = 0 := hbij.1 (by rw [hy0, map_zero])
    have hNt := (hc n hnM').1 t hc0
    funext b u
    by_cases hb : b = a
    · subst hb
      show N • y a u = 0
      rw [ht u]
      have e1 : N • t u = 0 := by simpa using congrFun hNt u
      rw [← cast_nsmul', ← smul_assoc, e1, zero_smul, cast_zero']
    · haveI := hsub b hb
      exact Subsingleton.elim _ _
  · obtain ⟨w, rfl⟩ := hbij.2 b
    obtain ⟨t, ht⟩ := (hc n hnM').2 w
    refine ⟨Pi.single a (fun u => (t u • one q (sch.obj (Spec A))).cast (by ring) rfl), ?_⟩
    rw [hform _ t (fun u => by rw [Pi.single_eq_same]), ht, map_nsmul]

/- English proof (translation)
Introduce `h6n h6r h9 hb2 q _ X R p A s hA hq i r c M N he hc n hn`. Distinguish the cases in `hneg : n < 0`. Conclude with `stalk_neg h9 q p A s i r c M N n hneg`. Conclude with `stalkTop_pf h6n h6r h9 hb2 h0 extOne_pf q p A s hA hq i r c M N he hc n (by omega) hn`.
-/
theorem Stalk_of (h0 : H0) : Stalk := by
  intro h6n h6r h9 hb2 q _ X R p A s hA hq i r c M N he hc n hn
  by_cases hneg : n < 0
  · exact stalk_neg h9 q p A s i r c M N n hneg
  · exact stalkTop_pf h6n h6r h9 hb2 h0 extOne_pf q p A s hA hq i r c M N he hc n (by omega) hn
