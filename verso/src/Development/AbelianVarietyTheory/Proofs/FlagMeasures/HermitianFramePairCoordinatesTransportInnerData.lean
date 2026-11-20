import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordDatum

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

/- English proof (translation)
Simplify using `[Coord.grp]`.
-/
lemma grp_apply (g : V ≃ₗ[E] V) (v : V) : c.grp g (c.e v) = c.e (g v) := by
  simp [Coord.grp]

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact hs x hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`.

Consider the case `smul a x _ hx => rw [map_smul, hx]`.
-/
lemma fix_span {W : Type} [AddCommGroup W] [Module E W] (g : W ≃ₗ[E] W) (s : Set W)
    (hs : ∀ x ∈ s, g x = x) : ∀ x ∈ Submodule.span E s, g x = x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

/- English proof (translation)
Unfold `Frames.H0`. Rewrite using `[Subgroup.mem_inf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, -, h2⟩`. Use `⟨h1, fun b => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Use `h2 (S.f b) (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩))` as an intermediate fact. Conclude with `sub_eq_zero.1 ((Submodule.mem_bot E).1 this)`. Use `h2 (S.f' b) (Submodule.mem_sup_right (Submodule.subset_span ⟨b, b.2, rfl⟩))` as an intermediate fact. Conclude with `sub_eq_zero.1 ((Submodule.mem_bot E).1 this)`. Introduce and unpack `⟨h1, h2⟩`.

Establish `hfix : ∀ v ∈ S.ME, g v = v`. Introduce `v hv`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hv`. Rewrite using `[map_add, fix_span g _ (by rintro _ ⟨i, -, rfl⟩; exact (h2 i).1) a ha, fix_span g _ (by rintro _ ⟨i, -, rfl⟩; exact (h2 i).2) b hb]`. Use `⟨h1, fun v => ⟨fun hv => ?_, fun hv => by rwa [hfix v hv]⟩, fun v hv => ?_⟩` and prove the remaining obligations.

Rewrite using `[← g.injective (hfix _ hv)]` and apply the resulting hypothesis. Rewrite using `[hfix v hv, sub_self]`. Conclude with `Submodule.zero_mem _`.
-/
lemma mem_riemannRochSpace_iff_regularAt_everywhere (g : S.GLV) : g ∈ S.H0 ↔ (∀ x y, S.h (g x) (g y) = S.h x y) ∧
    ∀ b, g (S.f b) = S.f b ∧ g (S.f' b) = S.f' b := by
  unfold Frames.H0
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, -, h2⟩
    refine ⟨h1, fun b => ⟨?_, ?_⟩⟩
    · have := h2 (S.f b) (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩))
      exact sub_eq_zero.1 ((Submodule.mem_bot E).1 this)
    · have := h2 (S.f' b) (Submodule.mem_sup_right (Submodule.subset_span ⟨b, b.2, rfl⟩))
      exact sub_eq_zero.1 ((Submodule.mem_bot E).1 this)
  · rintro ⟨h1, h2⟩
    have hfix : ∀ v ∈ S.ME, g v = v := by
      intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add, fix_span g _ (by rintro _ ⟨i, -, rfl⟩; exact (h2 i).1) a ha,
        fix_span g _ (by rintro _ ⟨i, -, rfl⟩; exact (h2 i).2) b hb]
    refine ⟨h1, fun v => ⟨fun hv => ?_, fun hv => by rwa [hfix v hv]⟩, fun v hv => ?_⟩
    · rwa [← g.injective (hfix _ hv)]
    · rw [hfix v hv, sub_self]; exact Submodule.zero_mem _

/- English proof (translation)
Rewrite using `[mem_riemannRochSpace_iff_regularAt_everywhere]`. Use `and_congr ⟨fun h x y => ?_, fun h x y => ?_⟩ (forall_congr' fun b => ?_)` and prove the remaining obligations. Take `⟨x, rfl⟩` from `c.e.surjective x`. Take `⟨y, rfl⟩` from `c.e.surjective y`. Rewrite using `[grp_apply, grp_apply, c.h_eq, c.h_eq, h]`.

Rewrite using `[← c.h_eq, ← c.h_eq, ← grp_apply, ← grp_apply, h]`. Rewrite using `[c.f_eq, c.f'_eq, grp_apply, grp_apply, c.e.injective.eq_iff, c.e.injective.eq_iff]`.
-/
lemma set_iff (g : V ≃ₗ[E] V) :
    (LocNG.IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b) ↔ c.grp g ∈ S.H0 := by
  rw [mem_riemannRochSpace_iff_regularAt_everywhere]
  refine and_congr ⟨fun h x y => ?_, fun h x y => ?_⟩ (forall_congr' fun b => ?_)
  · obtain ⟨x, rfl⟩ := c.e.surjective x
    obtain ⟨y, rfl⟩ := c.e.surjective y
    rw [grp_apply, grp_apply, c.h_eq, c.h_eq, h]
  · rw [← c.h_eq, ← c.h_eq, ← grp_apply, ← grp_apply, h]
  · rw [c.f_eq, c.f'_eq, grp_apply, grp_apply, c.e.injective.eq_iff, c.e.injective.eq_iff]

/- English proof (translation)
Establish `h : {g | LocNG.IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b} = (S.H0.comap c.grp.toMonoidHom : Subgroup (V ≃ₗ[E] V))`. Use extensionality with `g`. Conclude with `set_iff c g`. Unfold `LocNG.FPair.UW0`. Rewrite using `[h, Subgroup.closure_eq]`.

Both sides reduce to the same expression.
-/
lemma isUnitary_and_fixes_frames_of_mem_complementUnitary (g : V ≃ₗ[E] V) : g ∈ P.UW0 ↔ c.grp g ∈ S.H0 := by
  have h : {g | LocNG.IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b} =
      (S.H0.comap c.grp.toMonoidHom : Subgroup (V ≃ₗ[E] V)) := by
    ext g
    exact set_iff c g
  unfold LocNG.FPair.UW0
  rw [h, Subgroup.closure_eq]
  rfl

/- English proof (translation)
Establish `hX : ∀ x ∈ H.X f, g x = x` using `fix_span g _ (by rintro _ ⟨i, rfl⟩; exact hf _)`. Establish `key : ∀ x ∈ H.X f, H.h (g v) x = H.h v x` using `fun x hx => by`. Rewrite using `[← hu v x, hX x hx]`. Conclude with `⟨fun h x hx => (key x hx).symm.trans (h x hx), fun h x hx => (key x hx).trans (h x hx)⟩`.
-/
lemma perp_iff (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V) (hu : LocNG.IsUnitary H g)
    (hf : ∀ b, g (f b) = f b) (v : V) : g v ∈ H.perp (H.X f) ↔ v ∈ H.perp (H.X f) := by
  have hX : ∀ x ∈ H.X f, g x = x := fix_span g _ (by rintro _ ⟨i, rfl⟩; exact hf _)
  have key : ∀ x ∈ H.X f, H.h (g v) x = H.h v x := fun x hx => by
    rw [← hu v x, hX x hx]
  exact ⟨fun h x hx => (key x hx).symm.trans (h x hx), fun h x hx => (key x hx).trans (h x hx)⟩

/- English proof (translation)
Unfold `Coord.inn Coord.lat`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, h⟩`. Establish `h' : (x : V) = v` using `c.e.injective h`. Substitute `h'` using the available equality.

Conclude with `⟨x.2, hx⟩`. Introduce and unpack `⟨hv, h⟩`. Conclude with `⟨v, ⟨⟨v, hv⟩, h, rfl⟩, rfl⟩`.
-/
lemma mem_inn (f : Fin (r + 1) → V) (L : Submodule M.L.O (H.Wb f)) (v : V) :
    c.e v ∈ c.inn f L ↔ ∃ hv : v ∈ H.perp (H.X f), H.mkW f ⟨v, hv⟩ ∈ L := by
  unfold Coord.inn Coord.lat
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, h⟩
    have h' : (x : V) = v := c.e.injective h
    subst h'
    exact ⟨x.2, hx⟩
  · rintro ⟨hv, h⟩
    exact ⟨v, ⟨⟨v, hv⟩, h, rfl⟩, rfl⟩

/- English proof (translation)
Rewrite using `[mem_inn]`. Conclude with `⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩`.
-/
lemma mem_inn' (f : Fin (r + 1) → V) (L : Submodule M.L.O (H.Wb f)) (x : H.perp (H.X f)) :
    c.e x ∈ c.inn f L ↔ H.mkW f x ∈ L := by
  rw [mem_inn]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

/- English proof (translation)
Establish `h : ∀ v, g v ∈ g • A ↔ v ∈ A` using `fun v => by`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, hwv⟩`. Establish `: w = v` using `g.injective hwv`. Rewrite using `[← this]` and apply the resulting hypothesis.

Conclude with `fun hv => ⟨v, hv, rfl⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl v`. Conclude with `(h v).symm`. Introduce `h'`.

Use extensionality with `w`. Take `⟨v, rfl⟩` from `g.surjective w`. Rewrite using `[h, h']`.
-/
lemma smul_sub_iff (g : S.GLV) (A B : Submodule M.L.O S.V) :
    g • A = B ↔ ∀ v, v ∈ A ↔ g v ∈ B := by
  have h : ∀ v, g v ∈ g • A ↔ v ∈ A := fun v => by
    constructor
    · rintro ⟨w, hw, hwv⟩
      have : w = v := g.injective hwv
      rwa [← this]
    · exact fun hv => ⟨v, hv, rfl⟩
  constructor
  · rintro rfl v; exact (h v).symm
  · intro h'
    ext w
    obtain ⟨v, rfl⟩ := g.surjective w
    rw [h, h']

/- English proof (translation)
Establish `h : ∀ v' v, (g v', g v) ∈ g • A ↔ (v', v) ∈ A` using `fun v' v => Set.smul_mem_smul_set_iff (a := g) (x := (v', v))`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl v' v`. Conclude with `(h v' v).symm`. Introduce `h'`.

Use extensionality with `⟨w', w⟩`. Take `⟨v, rfl⟩` from `g.surjective w`. Take `⟨v', rfl⟩` from `g.surjective w'`. Rewrite using `[h, h']`.
-/
lemma smul_set_iff (g : S.GLV) (A B : Set (S.V × S.V)) :
    g • A = B ↔ ∀ v' v, (v', v) ∈ A ↔ (g v', g v) ∈ B := by
  have h : ∀ v' v, (g v', g v) ∈ g • A ↔ (v', v) ∈ A := fun v' v =>
    Set.smul_mem_smul_set_iff (a := g) (x := (v', v))
  constructor
  · rintro rfl v' v; exact (h v' v).symm
  · intro h'
    ext ⟨w', w⟩
    obtain ⟨v, rfl⟩ := g.surjective w
    obtain ⟨v', rfl⟩ := g.surjective w'
    rw [h, h']

/- English proof (translation)
Rewrite using `[smul_sub_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h v`. Take `⟨v, rfl⟩` from `c.e.surjective v`. Rewrite using `[grp_apply, mem_inn, mem_inn]`.

Conclude with `⟨fun ⟨hv, h1⟩ => ⟨(hp v).2 hv, (h ⟨v, hv⟩ ⟨_, (hp v).2 hv⟩ rfl).1 h1⟩, fun ⟨hv, h1⟩ => ⟨(hp v).1 hv, (h ⟨v, (hp v).1 hv⟩ ⟨_, hv⟩ rfl).2 h1⟩⟩`. Introduce `h x y hxy`. Rewrite using `[← mem_inn' c, ← mem_inn' c, h, grp_apply, hxy]`.
-/
lemma inn_move (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V)
    (hp : ∀ v, g v ∈ H.perp (H.X f) ↔ v ∈ H.perp (H.X f)) (L L' : Submodule M.L.O (H.Wb f)) :
    (∀ x y : ↥(H.perp (H.X f)), (y : V) = g x → (H.mkW f x ∈ L ↔ H.mkW f y ∈ L')) ↔
      c.grp g • c.inn f L = c.inn f L' := by
  rw [smul_sub_iff]
  constructor
  · intro h v
    obtain ⟨v, rfl⟩ := c.e.surjective v
    rw [grp_apply, mem_inn, mem_inn]
    exact ⟨fun ⟨hv, h1⟩ => ⟨(hp v).2 hv, (h ⟨v, hv⟩ ⟨_, (hp v).2 hv⟩ rfl).1 h1⟩,
      fun ⟨hv, h1⟩ => ⟨(hp v).1 hv, (h ⟨v, (hp v).1 hv⟩ ⟨_, hv⟩ rfl).2 h1⟩⟩
  · intro h x y hxy
    rw [← mem_inn' c, ← mem_inn' c, h, grp_apply, hxy]

def Q (d : LocNG.Datum P) (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))) : Prop :=
  (M.split = none ∧ H.mkW P.B.f x' ∈ d.L' ∧ H.mkW P.A.f x ∈ d.L) ∨
    (H.mkW P.B.f x', H.mkW P.A.f x) ∈ d.io

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x', x, h, hq⟩`. Establish `h1 : v' = x'` using `c.e.injective (congrArg Prod.fst h)`. Establish `h2 : v = x` using `c.e.injective (congrArg Prod.snd h)`. Substitute `h1 h2` using the available equality.

Conclude with `⟨x'.2, x.2, hq⟩`. Introduce and unpack `⟨hv', hv, hq⟩`. Conclude with `⟨⟨v', hv'⟩, ⟨v, hv⟩, rfl, hq⟩`.
-/
lemma mem_gr (d : LocNG.Datum P) (v' v : V) :
    (c.e v', c.e v) ∈ (c.dat d).2.2 ↔
      ∃ (hv' : v' ∈ H.perp (H.X P.B.f)) (hv : v ∈ H.perp (H.X P.A.f)), Q d ⟨v', hv'⟩ ⟨v, hv⟩ := by
  constructor
  · rintro ⟨x', x, h, hq⟩
    have h1 : v' = x' := c.e.injective (congrArg Prod.fst h)
    have h2 : v = x := c.e.injective (congrArg Prod.snd h)
    subst h1 h2
    exact ⟨x'.2, x.2, hq⟩
  · rintro ⟨hv', hv, hq⟩
    exact ⟨⟨v', hv'⟩, ⟨v, hv⟩, rfl, hq⟩

/- English proof (translation)
Rewrite using `[mem_gr]`. Conclude with `⟨fun ⟨_, _, h⟩ => h, fun h => ⟨x'.2, x.2, h⟩⟩`.
-/
lemma mem_gr' (d : LocNG.Datum P) (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))) :
    (c.e x', c.e x) ∈ (c.dat d).2.2 ↔ Q d x' x := by
  rw [mem_gr]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨x'.2, x.2, h⟩⟩

/- English proof (translation)
Take `⟨hu, hf⟩` from `(set_iff c g).2 ((isUnitary_and_fixes_frames_of_mem_complementUnitary c g).1 hg)`. Establish `hA` using `perp_iff P.A.f g hu fun b => (hf b).1`. Establish `hB` using `perp_iff P.B.f g hu fun b => (hf b).2`. Establish `hsplit : c.grp g • c.dat d = c.dat d' ↔ c.grp g • c.inn P.A.f d.L = c.inn P.A.f d'.L ∧ c.grp g • c.inn P.B.f d.L' = c.inn P.B.f d'.L' ∧ c.grp g • (c.dat d).2.2 = (c.dat d').2.2`. Rewrite using `[Prod.ext_iff, Prod.ext_iff]`.

Both sides reduce to the same expression. Establish `h3 : c.grp g • (c.dat d).2.2 = (c.dat d').2.2 ↔ ∀ (x' y' : ↥(H.perp (H.X P.B.f))) (x y : ↥(H.perp (H.X P.A.f))), (y' : V) = g x' → (y : V) = g x → (Q d x' x ↔ Q d' y' y)`. Rewrite using `[smul_set_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x' y' x y h1 h2`.

Rewrite using `[← mem_gr' c, ← mem_gr' c, h, grp_apply, grp_apply, h1, h2]`. Introduce `h v' v`. Take `⟨v, rfl⟩` from `c.e.surjective v`. Take `⟨v', rfl⟩` from `c.e.surjective v'`. Rewrite using `[grp_apply, grp_apply, mem_gr, mem_gr]`.

Conclude with `⟨fun ⟨hv', hv, h1⟩ => ⟨(hB v').2 hv', (hA v).2 hv, (h ⟨v', hv'⟩ ⟨_, (hB v').2 hv'⟩ ⟨v, hv⟩ ⟨_, (hA v).2 hv⟩ rfl rfl).1 h1⟩, fun ⟨hv', hv, h1⟩ => ⟨(hB v').1 hv', (hA v).1 hv, (h ⟨v', (hB v').1 hv'⟩ ⟨_, hv'⟩ ⟨v, (hA v).1 hv⟩ ⟨_, hv⟩ rfl rfl).2 h1⟩⟩`. Rewrite using `[hsplit, h3, ← inn_move c _ g hA, ← inn_move c _ g hB]`. Unfold `LocNG.Datum.Moves`. Use `and_congr_right fun h1 => and_congr_right fun h2 => ?_` and prove the remaining obligations. Use `forall₄_congr fun x' y' x y => forall₂_congr fun e1 e2 => ?_` and prove the remaining obligations.

Unfold `Q`. Distinguish the cases in `hs : M.split = none`. Simplify using `[d.io_L hs, d'.io_L hs, hs, h1 x y e2, h2 x' y' e1]`. Simplify using `[hs]`.
-/
lemma moves_iff (g : V ≃ₗ[E] V) (hg : g ∈ P.UW0) (d d' : LocNG.Datum P) :
    LocNG.Datum.Moves g d d' ↔ c.grp g • c.dat d = c.dat d' := by
  obtain ⟨hu, hf⟩ := (set_iff c g).2 ((isUnitary_and_fixes_frames_of_mem_complementUnitary c g).1 hg)
  have hA := perp_iff P.A.f g hu fun b => (hf b).1
  have hB := perp_iff P.B.f g hu fun b => (hf b).2
  have hsplit : c.grp g • c.dat d = c.dat d' ↔
      c.grp g • c.inn P.A.f d.L = c.inn P.A.f d'.L ∧ c.grp g • c.inn P.B.f d.L' = c.inn P.B.f d'.L' ∧
        c.grp g • (c.dat d).2.2 = (c.dat d').2.2 := by
    rw [Prod.ext_iff, Prod.ext_iff]; rfl
  have h3 : c.grp g • (c.dat d).2.2 = (c.dat d').2.2 ↔
      ∀ (x' y' : ↥(H.perp (H.X P.B.f))) (x y : ↥(H.perp (H.X P.A.f))), (y' : V) = g x' → (y : V) = g x →
        (Q d x' x ↔ Q d' y' y) := by
    rw [smul_set_iff]
    constructor
    · intro h x' y' x y h1 h2
      rw [← mem_gr' c, ← mem_gr' c, h, grp_apply, grp_apply, h1, h2]
    · intro h v' v
      obtain ⟨v, rfl⟩ := c.e.surjective v
      obtain ⟨v', rfl⟩ := c.e.surjective v'
      rw [grp_apply, grp_apply, mem_gr, mem_gr]
      exact ⟨fun ⟨hv', hv, h1⟩ => ⟨(hB v').2 hv', (hA v).2 hv,
          (h ⟨v', hv'⟩ ⟨_, (hB v').2 hv'⟩ ⟨v, hv⟩ ⟨_, (hA v).2 hv⟩ rfl rfl).1 h1⟩,
        fun ⟨hv', hv, h1⟩ => ⟨(hB v').1 hv', (hA v).1 hv,
          (h ⟨v', (hB v').1 hv'⟩ ⟨_, hv'⟩ ⟨v, (hA v).1 hv⟩ ⟨_, hv⟩ rfl rfl).2 h1⟩⟩
  rw [hsplit, h3, ← inn_move c _ g hA, ← inn_move c _ g hB]
  unfold LocNG.Datum.Moves
  refine and_congr_right fun h1 => and_congr_right fun h2 => ?_
  refine forall₄_congr fun x' y' x y => forall₂_congr fun e1 e2 => ?_
  unfold Q
  by_cases hs : M.split = none
  · simp [d.io_L hs, d'.io_L hs, hs, h1 x y e2, h2 x' y' e1]
  · simp [hs]

/- English proof (translation)
Unfold `LocNG.Datum.Stab`. Rewrite using `[← Subgroup.closure_eq ((S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)).comap c.grp.toMonoidHom)]`. Use `congr 1`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨(isUnitary_and_fixes_frames_of_mem_complementUnitary c g).1 h1, (moves_iff c g h1 d d).1 h2⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨(isUnitary_and_fixes_frames_of_mem_complementUnitary c g).2 h1, (moves_iff c g ((isUnitary_and_fixes_frames_of_mem_complementUnitary c g).2 h1) d d).2 h2⟩`.
-/
lemma stab_eq (d : LocNG.Datum P) : LocNG.Datum.Stab d =
    (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)).comap c.grp.toMonoidHom := by
  unfold LocNG.Datum.Stab
  rw [← Subgroup.closure_eq ((S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)).comap c.grp.toMonoidHom)]
  congr 1
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(isUnitary_and_fixes_frames_of_mem_complementUnitary c g).1 h1, (moves_iff c g h1 d d).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(isUnitary_and_fixes_frames_of_mem_complementUnitary c g).2 h1, (moves_iff c g ((isUnitary_and_fixes_frames_of_mem_complementUnitary c g).2 h1) d d).2 h2⟩

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Use `show c.e (g (c.e.symm (c.e v))) = _`. Simplify using the standard rewrite rules.
-/
private theorem grp_apply_e (g : V ≃ₗ[E] V) (v : V) :
    c.grp g (c.e v) = c.e (g v) := by
  show c.e (g (c.e.symm (c.e v))) = _
  simp

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Use `⟨fun v => ⟨fun h => ?_, fun h => by rwa [hN v h]⟩, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h2` using `T.injective (hN _ h)`. Rewrite `h` using `[h2]`. Then use the resulting hypothesis. Rewrite using `[hN v hv, sub_self]`. Conclude with `zero_mem _`.
-/
private theorem mapsTo_and_sub_mem_bot_of_fixes {W : Type} [AddCommGroup W] [Module E W] (T : W ≃ₗ[E] W)
    (N : Submodule E W) (hN : ∀ v ∈ N, T v = v) :
    (∀ v, T v ∈ N ↔ v ∈ N) ∧ ∀ v ∈ N, T v - v ∈ (⊥ : Submodule E W) := by
  refine ⟨fun v => ⟨fun h => ?_, fun h => by rwa [hN v h]⟩, fun v hv => ?_⟩
  · have h2 := T.injective (hN _ h)
    rwa [h2] at h
  · rw [hN v hv, sub_self]
    exact zero_mem _

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Establish `hT` using `grp_apply_e c g`. Simplify using `only [_root_.GlobalTheory.HL.Frames.H0, Subgroup.mem_inf]`. Unfold `_root_.GlobalTheory.HL.isomG _root_.GlobalTheory.HL.unipOn _root_.GlobalTheory.HL.Frames.ME _root_.GlobalTheory.HL.Frames.spanTo`. Simplify using `only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hiso, hfix⟩`. Use `⟨fun x y => ?_, mapsTo_and_sub_mem_bot_of_fixes _ _ ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `c.e.surjective x`. Take `⟨y, rfl⟩` from `c.e.surjective y`. Rewrite using `[hT, hT]`.

Conclude with `(c.h_eq _ _).trans ((hiso x y).trans (c.h_eq x y).symm)`. It suffices to establish `h : _ ≤ LinearMap.eqLocus (c.grp g : S.V →ₗ[E] S.V) LinearMap.id from fun v hv => h hv`. Apply the tactic sequence `refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_) <;>`. Apply the tactic sequence `rintro _ ⟨i, -, rfl⟩ <;>`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_eqLocus, LinearEquiv.coe_coe, LinearMap.id_apply, c.f_eq, c.f'_eq, hT, (hfix i).1, (hfix i).2]`.

Introduce and unpack `⟨hiso, hun⟩`. Use `⟨fun x y => ?_, fun b => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `h` using `hiso (c.e x) (c.e y)`. Rewrite `h` using `[hT, hT]`. Rewrite using `[← c.h_eq (g x) (g y), ← c.h_eq x y]`.

Conclude with `h`. Establish `h` using `hun.2 _ (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.isLt, rfl⟩))`. Rewrite `h` using `[Submodule.mem_bot, sub_eq_zero, c.f_eq, hT]`. Conclude with `c.e.injective h`. Establish `h` using `hun.2 _ (Submodule.mem_sup_right (Submodule.subset_span ⟨b, b.isLt, rfl⟩))`.

Rewrite `h` using `[Submodule.mem_bot, sub_eq_zero, c.f'_eq, hT]`. Conclude with `c.e.injective h`.
-/
private theorem isometry_fixing_frames_iff_grp_mem_H0 (g : V ≃ₗ[E] V) :
    ((∀ x y, H.h (g x) (g y) = H.h x y) ∧
      ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b) ↔
      c.grp g ∈ S.H0 := by
  have hT := grp_apply_e c g
  simp only [_root_.GlobalTheory.HL.Frames.H0, Subgroup.mem_inf]
  unfold _root_.GlobalTheory.HL.isomG _root_.GlobalTheory.HL.unipOn _root_.GlobalTheory.HL.Frames.ME
    _root_.GlobalTheory.HL.Frames.spanTo
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hiso, hfix⟩
    refine ⟨fun x y => ?_, mapsTo_and_sub_mem_bot_of_fixes _ _ ?_⟩
    · obtain ⟨x, rfl⟩ := c.e.surjective x
      obtain ⟨y, rfl⟩ := c.e.surjective y
      rw [hT, hT]
      exact (c.h_eq _ _).trans ((hiso x y).trans (c.h_eq x y).symm)
    · suffices h : _ ≤ LinearMap.eqLocus (c.grp g : S.V →ₗ[E] S.V)
          LinearMap.id from fun v hv => h hv
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_) <;>
        rintro _ ⟨i, -, rfl⟩ <;>
        simp only [SetLike.mem_coe, LinearMap.mem_eqLocus, LinearEquiv.coe_coe, LinearMap.id_apply,
          c.f_eq, c.f'_eq, hT, (hfix i).1, (hfix i).2]
  · rintro ⟨hiso, hun⟩
    refine ⟨fun x y => ?_, fun b => ⟨?_, ?_⟩⟩
    · have h := hiso (c.e x) (c.e y)
      rw [hT, hT] at h
      rw [← c.h_eq (g x) (g y), ← c.h_eq x y]
      exact h
    · have h := hun.2 _ (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.isLt, rfl⟩))
      rw [Submodule.mem_bot, sub_eq_zero, c.f_eq, hT] at h
      exact c.e.injective h
    · have h := hun.2 _ (Submodule.mem_sup_right (Submodule.subset_span ⟨b, b.isLt, rfl⟩))
      rw [Submodule.mem_bot, sub_eq_zero, c.f'_eq, hT] at h
      exact c.e.injective h

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `hle : P.UW0 ≤ S.H0.comap c.grp.toMonoidHom`. Unfold `_root_.Formalism.MainNotions.S.LocNG.FPair.UW0`. Rewrite using `[Subgroup.closure_le]`.

Introduce `x hx`. Conclude with `(isometry_fixing_frames_iff_grp_mem_H0 c x).1 ⟨hx.1, hx.2⟩`. Conclude with `hle hg`. Introduce `hg`. Unfold `_root_.Formalism.MainNotions.S.LocNG.FPair.UW0`.

Apply `Subgroup.subset_closure` to reduce the goal to its premises. Establish `h` using `(isometry_fixing_frames_iff_grp_mem_H0 c g).2 hg`. Conclude with `⟨h.1, h.2⟩`.
-/
private theorem mem_UW0_iff_grp_mem_H0 (g : V ≃ₗ[E] V) :
    g ∈ P.UW0 ↔ c.grp g ∈ S.H0 := by
  constructor
  · intro hg
    have hle : P.UW0 ≤
        S.H0.comap c.grp.toMonoidHom := by
      unfold _root_.Formalism.MainNotions.S.LocNG.FPair.UW0
      rw [Subgroup.closure_le]
      intro x hx
      exact (isometry_fixing_frames_iff_grp_mem_H0 c x).1 ⟨hx.1, hx.2⟩
    exact hle hg
  · intro hg
    unfold _root_.Formalism.MainNotions.S.LocNG.FPair.UW0
    apply Subgroup.subset_closure
    have h := (isometry_fixing_frames_iff_grp_mem_H0 c g).2 hg
    exact ⟨h.1, h.2⟩

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Establish `hX : ∀ x ∈ H.X f, g x = x`. Establish `h : H.X f ≤ LinearMap.eqLocus (g : V →ₗ[E] V) LinearMap.id`. Unfold `_root_.Formalism.MainNotions.S.Loc.HermSp.X`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Simplify using `only [SetLike.mem_coe, LinearMap.mem_eqLocus, LinearEquiv.coe_coe, LinearMap.id_apply, hf]`. Conclude with `fun x hx => h hx`. Unfold `_root_.Formalism.MainNotions.S.Loc.HermSp.perp`. Simplify using `only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]`. Use `forall₂_congr fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[← hiso v x, hX x hx]`.
-/
private theorem apply_mem_perp_X_iff_of_isometry_fixing (g : V ≃ₗ[E] V) (hiso : ∀ x y, H.h (g x) (g y) = H.h x y)
    (f : Fin (r + 1) → V) (hf : ∀ b, g (f b) = f b) (v : V) :
    g v ∈ H.perp (H.X f) ↔ v ∈ H.perp (H.X f) := by
  have hX : ∀ x ∈ H.X f, g x = x := by
    have h : H.X f ≤ LinearMap.eqLocus (g : V →ₗ[E] V) LinearMap.id := by
      unfold _root_.Formalism.MainNotions.S.Loc.HermSp.X
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_eqLocus, LinearEquiv.coe_coe,
        LinearMap.id_apply, hf]
    exact fun x hx => h hx
  unfold _root_.Formalism.MainNotions.S.Loc.HermSp.perp
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  refine forall₂_congr fun x hx => ?_
  rw [← hiso v x, hX x hx]

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hs x y hxy`. Prove the components needed by the constructor for the conclusion. Introduce `hp`. Establish `hmem : (g x : X) ∈ g '' {v | ∃ h : K v, p ⟨v, h⟩}` using `⟨x, ⟨x.2, hp⟩, rfl⟩`.

Rewrite `hmem` using `[hs]`. Take `⟨h, hq⟩` from `hmem`. Establish `hy : y = ⟨g x, h⟩` using `Subtype.ext hxy`. Rewrite using `[hy]` and apply the resulting hypothesis. Introduce `hq`.

Establish `hmem : (y : X) ∈ {v | ∃ h : K v, q ⟨v, h⟩}` using `⟨y.2, hq⟩`. Rewrite `hmem` using `[← hs]`. Take `⟨w, ⟨hw, hpw⟩, hwy⟩` from `hmem`. Establish `hwx : w = x` using `g.injective (hwy.trans hxy)`. Substitute `hwx` using the available equality.

Conclude with `hpw`. Introduce `h`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, ⟨hw, hp⟩, rfl⟩`.

Conclude with `⟨(hK w).2 hw, (h ⟨w, hw⟩ ⟨g w, (hK w).2 hw⟩ rfl).1 hp⟩`. Introduce and unpack `⟨hv, hq⟩`. Establish `hw : K (g.symm v)`. Rewrite using `[← hK]`. Simplify using `using hv`.

Conclude with `⟨g.symm v, ⟨hw, (h ⟨g.symm v, hw⟩ ⟨v, hv⟩ (by simp)).2 hq⟩, by simp⟩`.
-/
private theorem image_setOf_subtype_eq_iff {X : Type} (g : X ≃ X) (K : X → Prop)
    (hK : ∀ v, K (g v) ↔ K v) (p q : {v // K v} → Prop) :
    g '' {v | ∃ h : K v, p ⟨v, h⟩} = {v | ∃ h : K v, q ⟨v, h⟩} ↔
      ∀ x y : {v // K v}, (y : X) = g x → (p x ↔ q y) := by
  constructor
  · intro hs x y hxy
    constructor
    · intro hp
      have hmem : (g x : X) ∈ g '' {v | ∃ h : K v, p ⟨v, h⟩} := ⟨x, ⟨x.2, hp⟩, rfl⟩
      rw [hs] at hmem
      obtain ⟨h, hq⟩ := hmem
      have hy : y = ⟨g x, h⟩ := Subtype.ext hxy
      rwa [hy]
    · intro hq
      have hmem : (y : X) ∈ {v | ∃ h : K v, q ⟨v, h⟩} := ⟨y.2, hq⟩
      rw [← hs] at hmem
      obtain ⟨w, ⟨hw, hpw⟩, hwy⟩ := hmem
      have hwx : w = x := g.injective (hwy.trans hxy)
      subst hwx
      exact hpw
  · intro h
    ext v
    constructor
    · rintro ⟨w, ⟨hw, hp⟩, rfl⟩
      exact ⟨(hK w).2 hw, (h ⟨w, hw⟩ ⟨g w, (hK w).2 hw⟩ rfl).1 hp⟩
    · rintro ⟨hv, hq⟩
      have hw : K (g.symm v) := by
        rw [← hK]
        simpa using hv
      exact ⟨g.symm v, ⟨hw, (h ⟨g.symm v, hw⟩ ⟨v, hv⟩ (by simp)).2 hq⟩, by simp⟩

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Establish `hT` using `grp_apply_e c g`. Establish `hc : ∀ N : Submodule M.L.O (H.Wb f), (c.inn f N : Set S.V) = c.e '' {v | ∃ h : v ∈ H.perp (H.X f), H.mkW f ⟨v, h⟩ ∈ N}`. Introduce `N`. Use extensionality with `w`. Simplify using `only [_root_.GlobalTheory.HL.Coord.inn, _root_.GlobalTheory.HL.Coord.lat, SetLike.mem_coe, Submodule.mem_map, Submodule.mem_comap, Set.mem_image, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨z, hz, rfl⟩, rfl⟩`. Conclude with `⟨z, ⟨z.2, hz⟩, rfl⟩`. Introduce and unpack `⟨v, ⟨h, hv⟩, rfl⟩`. Conclude with `⟨v, ⟨⟨v, h⟩, hv, rfl⟩, rfl⟩`.

Rewrite using `[← SetLike.coe_set_eq, Submodule.coe_pointwise_smul, hc, hc, ← Set.image_smul, Set.image_image]`. Rewrite using `[show (fun v => c.grp g • c.e v) = c.e ∘ g.toEquiv from funext fun v => by`. Simplify using `[LinearEquiv.smul_def, hT]]`. Rewrite using `[Set.image_comp, (Set.image_injective.2 c.e.injective).eq_iff]`. Conclude with `image_setOf_subtype_eq_iff g.toEquiv (· ∈ H.perp (H.X f)) hK (fun x => H.mkW f x ∈ L) (fun y => H.mkW f y ∈ L')`.
-/
private theorem grp_smul_inn_eq_inn_iff (g : V ≃ₗ[E] V) (f : Fin (r + 1) → V)
    (hK : ∀ v, g v ∈ H.perp (H.X f) ↔ v ∈ H.perp (H.X f))
    (L L' : Submodule M.L.O (H.Wb f)) :
    c.grp g • c.inn f L =
        c.inn f L' ↔
      ∀ x y : ↥(H.perp (H.X f)), (y : V) = g x → (H.mkW f x ∈ L ↔ H.mkW f y ∈ L') := by
  have hT := grp_apply_e c g
  have hc : ∀ N : Submodule M.L.O (H.Wb f), (c.inn f N : Set S.V) =
      c.e '' {v | ∃ h : v ∈ H.perp (H.X f), H.mkW f ⟨v, h⟩ ∈ N} := by
    intro N
    ext w
    simp only [_root_.GlobalTheory.HL.Coord.inn,
      _root_.GlobalTheory.HL.Coord.lat, SetLike.mem_coe, Submodule.mem_map,
      Submodule.mem_comap, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, ⟨z.2, hz⟩, rfl⟩
    · rintro ⟨v, ⟨h, hv⟩, rfl⟩
      exact ⟨v, ⟨⟨v, h⟩, hv, rfl⟩, rfl⟩
  rw [← SetLike.coe_set_eq, Submodule.coe_pointwise_smul, hc, hc, ← Set.image_smul,
    Set.image_image]
  rw [show (fun v => c.grp g • c.e v) =
      c.e ∘ g.toEquiv from funext fun v => by
        simp [LinearEquiv.smul_def, hT]]
  rw [Set.image_comp, (Set.image_injective.2 c.e.injective).eq_iff]
  exact image_setOf_subtype_eq_iff g.toEquiv (· ∈ H.perp (H.X f)) hK (fun x => H.mkW f x ∈ L)
    (fun y => H.mkW f y ∈ L')

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Establish `hT` using `grp_apply_e c g`. Set `K : V × V → Prop` to `fun v => v.1 ∈ H.perp (H.X P.B.f) ∧ v.2 ∈ H.perp (H.X P.A.f)`. Establish `hZ : ∀ d : _root_.Formalism.MainNotions.S.LocNG.Datum P, {p : S.V × S.V | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))), p = (c.e x', c.e x) ∧ _root_.GlobalTheory.HL.CoordDatum.Q d x' x} = Prod.map c.e c.e '' {v | ∃ h : K v, _root_.GlobalTheory.HL.CoordDatum.Q d ⟨v.1 …`. Introduce `d`. Use extensionality with `p`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x', x, rfl, hq⟩`. Conclude with `⟨((x' : V), (x : V)), ⟨⟨x'.2, x.2⟩, hq⟩, rfl⟩`. Introduce and unpack `⟨v, ⟨h, hq⟩, rfl⟩`. Conclude with `⟨⟨v.1, h.1⟩, ⟨v.2, h.2⟩, rfl, hq⟩`.

Establish `hK : ∀ v, K (Equiv.prodCongr g.toEquiv g.toEquiv v) ↔ K v` using `fun v => and_congr (hKB v.1) (hKA v.2)`. Establish `hinj : Function.Injective (Prod.map c.e c.e)` using `c.e.injective.prodMap c.e.injective`. Rewrite using `[hZ, hZ, ← Set.image_smul, Set.image_image]`. Rewrite using `[show (fun v => c.grp g • Prod.map c.e c.e v) = Prod.map c.e c.e ∘ Equiv.prodCongr g.toEquiv g.toEquiv from`. Use function extensionality and compare the values at `fun v => by`.

Take `⟨a, b⟩` from `v`. Simplify using `[Prod.smul_mk, LinearEquiv.smul_def, hT]]`. Rewrite using `[Set.image_comp, (Set.image_injective.2 hinj).eq_iff]`. Use `(image_setOf_subtype_eq_iff _ K hK (fun v => _root_.GlobalTheory.HL.CoordDatum.Q d ⟨v.1.1, v.2.1⟩ ⟨v.1.2, v.2.2⟩) (fun v => _root_.GlobalTheory.HL.CoordDatum.Q d' ⟨v.1.1, v.2.1⟩ ⟨v.1.2, v.2.2⟩)).trans ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce `h x' y' x y hy' hy`. Conclude with `h ⟨((x' : V), (x : V)), x'.2, x.2⟩ ⟨((y' : V), (y : V)), y'.2, y.2⟩ (Prod.ext hy' hy)`. Introduce and unpack `h ⟨⟨a, b⟩, ha, hb⟩ ⟨⟨a', b'⟩, ha', hb'⟩ hy`. Establish `hy2` using `Prod.ext_iff.1 hy`. Conclude with `h ⟨a, ha⟩ ⟨a', ha'⟩ ⟨b, hb⟩ ⟨b', hb'⟩ hy2.1 hy2.2`.
-/
private theorem graph_transport_iff_lemma_11 (g : V ≃ₗ[E] V)
    (hKB : ∀ v, g v ∈ H.perp (H.X P.B.f) ↔ v ∈ H.perp (H.X P.B.f))
    (hKA : ∀ v, g v ∈ H.perp (H.X P.A.f) ↔ v ∈ H.perp (H.X P.A.f)) (d d' : _root_.Formalism.MainNotions.S.LocNG.Datum P) :
    c.grp g • {p : S.V × S.V | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))),
          p = (c.e x', c.e x) ∧ _root_.GlobalTheory.HL.CoordDatum.Q d x' x} =
      {p : S.V × S.V | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))),
          p = (c.e x', c.e x) ∧
        _root_.GlobalTheory.HL.CoordDatum.Q d' x' x} ↔
      ∀ (x' y' : ↥(H.perp (H.X P.B.f))) (x y : ↥(H.perp (H.X P.A.f))), (y' : V) = g x' →
        (y : V) = g x → (_root_.GlobalTheory.HL.CoordDatum.Q d x' x ↔ _root_.GlobalTheory.HL.CoordDatum.Q d' y' y) := by
  have hT := grp_apply_e c g
  let K : V × V → Prop := fun v => v.1 ∈ H.perp (H.X P.B.f) ∧ v.2 ∈ H.perp (H.X P.A.f)
  have hZ : ∀ d : _root_.Formalism.MainNotions.S.LocNG.Datum P, {p : S.V × S.V | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))),
          p = (c.e x', c.e x) ∧ _root_.GlobalTheory.HL.CoordDatum.Q d x' x} =
      Prod.map c.e c.e ''
        {v | ∃ h : K v, _root_.GlobalTheory.HL.CoordDatum.Q d ⟨v.1, h.1⟩ ⟨v.2, h.2⟩} := by
    intro d
    ext p
    constructor
    · rintro ⟨x', x, rfl, hq⟩
      exact ⟨((x' : V), (x : V)), ⟨⟨x'.2, x.2⟩, hq⟩, rfl⟩
    · rintro ⟨v, ⟨h, hq⟩, rfl⟩
      exact ⟨⟨v.1, h.1⟩, ⟨v.2, h.2⟩, rfl, hq⟩
  have hK : ∀ v, K (Equiv.prodCongr g.toEquiv g.toEquiv v) ↔ K v := fun v =>
    and_congr (hKB v.1) (hKA v.2)
  have hinj : Function.Injective (Prod.map c.e c.e) :=
    c.e.injective.prodMap c.e.injective
  rw [hZ, hZ, ← Set.image_smul, Set.image_image]
  rw [show (fun v => c.grp g • Prod.map c.e c.e v) =
      Prod.map c.e c.e ∘ Equiv.prodCongr g.toEquiv g.toEquiv from
      funext fun v => by
        obtain ⟨a, b⟩ := v
        simp [Prod.smul_mk, LinearEquiv.smul_def, hT]]
  rw [Set.image_comp, (Set.image_injective.2 hinj).eq_iff]
  refine (image_setOf_subtype_eq_iff _ K hK
    (fun v => _root_.GlobalTheory.HL.CoordDatum.Q d ⟨v.1.1, v.2.1⟩ ⟨v.1.2, v.2.2⟩)
    (fun v => _root_.GlobalTheory.HL.CoordDatum.Q d' ⟨v.1.1, v.2.1⟩ ⟨v.1.2, v.2.2⟩)).trans ?_
  constructor
  · intro h x' y' x y hy' hy
    exact h ⟨((x' : V), (x : V)), x'.2, x.2⟩ ⟨((y' : V), (y : V)), y'.2, y.2⟩ (Prod.ext hy' hy)
  · rintro h ⟨⟨a, b⟩, ha, hb⟩ ⟨⟨a', b'⟩, ha', hb'⟩ hy
    have hy2 := Prod.ext_iff.1 hy
    exact h ⟨a, ha⟩ ⟨a', ha'⟩ ⟨b, hb⟩ ⟨b', hb'⟩ hy2.1 hy2.2

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Take `⟨hiso, hfix⟩` from `(isometry_fixing_frames_iff_grp_mem_H0 c g).2 ((mem_UW0_iff_grp_mem_H0 c g).1 hg)`. Establish `hKA` using `apply_mem_perp_X_iff_of_isometry_fixing g hiso P.A.f (fun b => (hfix b).1)`. Establish `hKB` using `apply_mem_perp_X_iff_of_isometry_fixing g hiso P.B.f (fun b => (hfix b).2)`. Establish `hdat : ∀ d : _root_.Formalism.MainNotions.S.LocNG.Datum P, c.dat d = (c.inn P.A.f d.L, c.inn P.B.f d.L', {p : S.V × S.V | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))), p = (c.e x', c.e x) ∧ _root_.GlobalTheory.HL.CoordDatum.Q d x' x})` using `fun _ => rfl`. Unfold `_root_.Formalism.MainNotions.S.LocNG.Datum.Moves`.

Rewrite using `[hdat, hdat, Prod.smul_mk, Prod.smul_mk, Prod.mk.injEq, Prod.mk.injEq, grp_smul_inn_eq_inn_iff c g _ hKA, grp_smul_inn_eq_inn_iff c g _ hKB, graph_transport_iff_lemma_11 c g hKB hKA]`. Use `and_congr_right fun c1 => and_congr_right fun c2 => ?_` and prove the remaining obligations. Break down `hs : M.split with _ | s` into its components or cases. Establish `e1` using `d.6 hs`. Establish `e2` using `d'.6 hs`.

Prove the components needed by the constructor for the conclusion. Introduce `_ x' y' x y hy' hy`. Simplify using `only [_root_.GlobalTheory.HL.CoordDatum.Q, hs, e1, e2, Set.mem_empty_iff_false, or_false, true_and]`. Conclude with `and_congr (c2 x' y' hy') (c1 x y hy)`. Introduce `_ x' y' x y _ _`.

Simplify using `only [e1, e2, Set.mem_empty_iff_false]`. Simplify using `only [_root_.GlobalTheory.HL.CoordDatum.Q, hs, reduceCtorEq, false_and, false_or]`.
-/
private theorem Datum_moves_iff_grp_smul_dat_eq (g : V ≃ₗ[E] V) (hg : g ∈ P.UW0) (d d' : _root_.Formalism.MainNotions.S.LocNG.Datum P) :
    _root_.Formalism.MainNotions.S.LocNG.Datum.Moves g d d' ↔
      c.grp g • c.dat d = c.dat d' := by
  obtain ⟨hiso, hfix⟩ := (isometry_fixing_frames_iff_grp_mem_H0 c g).2 ((mem_UW0_iff_grp_mem_H0 c g).1 hg)
  have hKA := apply_mem_perp_X_iff_of_isometry_fixing g hiso P.A.f (fun b => (hfix b).1)
  have hKB := apply_mem_perp_X_iff_of_isometry_fixing g hiso P.B.f (fun b => (hfix b).2)
  have hdat : ∀ d : _root_.Formalism.MainNotions.S.LocNG.Datum P, c.dat d =
      (c.inn P.A.f d.L, c.inn P.B.f d.L',
        {p : S.V × S.V | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))),
          p = (c.e x', c.e x) ∧
          _root_.GlobalTheory.HL.CoordDatum.Q d x' x}) := fun _ => rfl
  unfold _root_.Formalism.MainNotions.S.LocNG.Datum.Moves
  rw [hdat, hdat, Prod.smul_mk, Prod.smul_mk, Prod.mk.injEq, Prod.mk.injEq,
    grp_smul_inn_eq_inn_iff c g _ hKA, grp_smul_inn_eq_inn_iff c g _ hKB,
    graph_transport_iff_lemma_11 c g hKB hKA]
  refine and_congr_right fun c1 => and_congr_right fun c2 => ?_
  rcases hs : M.split with _ | s
  · have e1 := d.6 hs
    have e2 := d'.6 hs
    constructor
    · intro _ x' y' x y hy' hy
      simp only [_root_.GlobalTheory.HL.CoordDatum.Q, hs, e1, e2, Set.mem_empty_iff_false, or_false,
        true_and]
      exact and_congr (c2 x' y' hy') (c1 x y hy)
    · intro _ x' y' x y _ _
      simp only [e1, e2, Set.mem_empty_iff_false]
  · simp only [_root_.GlobalTheory.HL.CoordDatum.Q, hs, reduceCtorEq, false_and, false_or]

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Unfold `_root_.Formalism.MainNotions.S.Loc.HermSp.mkW`. Conclude with `Submodule.mkQ_surjective _`.
-/
private theorem mkW_surjective (f : Fin (r + 1) → V) : Function.Surjective (H.mkW f) := by
  unfold _root_.Formalism.MainNotions.S.Loc.HermSp.mkW
  exact Submodule.mkQ_surjective _

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Introduce `d d' hdd`. Establish `hm` using `(Datum_moves_iff_grp_smul_dat_eq c 1 (one_mem _) d d').2 (by rw [map_one, one_smul]; exact hdd)`. Take `⟨h1, h2, h3⟩` from `hm`. Take `⟨L, L', hL, hL', io, hio⟩` from `d`. Take `⟨N, N', hN, hN', jo, hjo⟩` from `d'`.

Establish `hLN : L = N`. Use extensionality with `w`. Take `⟨x, rfl⟩` from `mkW_surjective P.A.f w`. Conclude with `h1 x x rfl`. Establish `hLN' : L' = N'`.

Use extensionality with `w`. Take `⟨x, rfl⟩` from `mkW_surjective P.B.f w`. Conclude with `h2 x x rfl`. Establish `hio' : io = jo`. Use extensionality with `⟨a, b⟩`.

Take `⟨x', rfl⟩` from `mkW_surjective P.B.f a`. Take `⟨x, rfl⟩` from `mkW_surjective P.A.f b`. Conclude with `h3 x' x' x x rfl rfl`. Substitute `hLN hLN' hio'` using the available equality. Both sides reduce to the same expression.
-/
private theorem dat_injective : Function.Injective c.dat := by
  intro d d' hdd
  have hm := (Datum_moves_iff_grp_smul_dat_eq c 1 (one_mem _) d d').2 (by rw [map_one, one_smul]; exact hdd)
  obtain ⟨h1, h2, h3⟩ := hm
  obtain ⟨L, L', hL, hL', io, hio⟩ := d
  obtain ⟨N, N', hN, hN', jo, hjo⟩ := d'
  have hLN : L = N := by
    ext w
    obtain ⟨x, rfl⟩ := mkW_surjective P.A.f w
    exact h1 x x rfl
  have hLN' : L' = N' := by
    ext w
    obtain ⟨x, rfl⟩ := mkW_surjective P.B.f w
    exact h2 x x rfl
  have hio' : io = jo := by
    ext ⟨a, b⟩
    obtain ⟨x', rfl⟩ := mkW_surjective P.B.f a
    obtain ⟨x, rfl⟩ := mkW_surjective P.A.f b
    exact h3 x' x' x x rfl rfl
  subst hLN hLN' hio'
  rfl

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Unfold `_root_.Formalism.MainNotions.S.LocNG.Datum.Rel`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, hm⟩`. Conclude with `⟨_, (mem_UW0_iff_grp_mem_H0 c g).1 hg, (Datum_moves_iff_grp_smul_dat_eq c g hg d d').1 hm⟩`. Introduce and unpack `⟨h, hh, he⟩`.

Take `⟨g, rfl⟩` from `c.grp.surjective h`. Establish `hg` using `(mem_UW0_iff_grp_mem_H0 c g).2 hh`. Conclude with `⟨g, hg, (Datum_moves_iff_grp_smul_dat_eq c g hg d d').2 he⟩`.
-/
private theorem Datum_rel_iff_exists_H0_smul_dat_eq (d d' : _root_.Formalism.MainNotions.S.LocNG.Datum P) :
    _root_.Formalism.MainNotions.S.LocNG.Datum.Rel d d' ↔ ∃ h ∈ S.H0,
      h • c.dat d = c.dat d' := by
  unfold _root_.Formalism.MainNotions.S.LocNG.Datum.Rel
  constructor
  · rintro ⟨g, hg, hm⟩
    exact ⟨_, (mem_UW0_iff_grp_mem_H0 c g).1 hg, (Datum_moves_iff_grp_smul_dat_eq c g hg d d').1 hm⟩
  · rintro ⟨h, hh, he⟩
    obtain ⟨g, rfl⟩ := c.grp.surjective h
    have hg := (mem_UW0_iff_grp_mem_H0 c g).2 hh
    exact ⟨g, hg, (Datum_moves_iff_grp_smul_dat_eq c g hg d d').2 he⟩

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Unfold `_root_.Formalism.MainNotions.S.LocNG.Datum.Stab`. Establish `hset : {g | g ∈ P.UW0 ∧ _root_.Formalism.MainNotions.S.LocNG.Datum.Moves g d d} = ((S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)).comap c.grp.toMonoidHom : Set (V ≃ₗ[E] V))`. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulEquiv.coe_toMonoidHom]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hg, hm⟩`. Conclude with `⟨(mem_UW0_iff_grp_mem_H0 c g).1 hg, (Datum_moves_iff_grp_smul_dat_eq c g hg d d).1 hm⟩`. Introduce and unpack `⟨hg, hs⟩`. Establish `hg'` using `(mem_UW0_iff_grp_mem_H0 c g).2 hg`. Conclude with `⟨hg', (Datum_moves_iff_grp_smul_dat_eq c g hg' d d).2 hs⟩`.

Rewrite using `[hset, Subgroup.closure_eq]`.
-/
private theorem Datum_stab_eq_comap_H0_inf_stabilizer (d : _root_.Formalism.MainNotions.S.LocNG.Datum P) :
    _root_.Formalism.MainNotions.S.LocNG.Datum.Stab d = (S.H0 ⊓
      MulAction.stabilizer S.GLV (c.dat d)).comap
        c.grp.toMonoidHom := by
  unfold _root_.Formalism.MainNotions.S.LocNG.Datum.Stab
  have hset : {g | g ∈ P.UW0 ∧ _root_.Formalism.MainNotions.S.LocNG.Datum.Moves g d d} =
      ((S.H0 ⊓ MulAction.stabilizer S.GLV
        (c.dat d)).comap c.grp.toMonoidHom :
          Set (V ≃ₗ[E] V)) := by
    ext g
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_inf,
      MulAction.mem_stabilizer_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨hg, hm⟩
      exact ⟨(mem_UW0_iff_grp_mem_H0 c g).1 hg, (Datum_moves_iff_grp_smul_dat_eq c g hg d d).1 hm⟩
    · rintro ⟨hg, hs⟩
      have hg' := (mem_UW0_iff_grp_mem_H0 c g).2 hg
      exact ⟨hg', (Datum_moves_iff_grp_smul_dat_eq c g hg' d d).2 hs⟩
  rw [hset, Subgroup.closure_eq]

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
/- English proof (translation)
Rewrite using `[Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective f.surjective]`.
-/
private theorem relIndex_comap_mulEquiv {G G' : Type} [Group G] [Group G'] (f : G ≃* G')
    (A B : Subgroup G') :
    (A.comap f.toMonoidHom).relIndex (B.comap f.toMonoidHom) = A.relIndex B := by
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective f.surjective]

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M _ V _ _ H r k P S c`. Use `⟨dat_injective c, fun g hg d d' => Datum_moves_iff_grp_smul_dat_eq c g hg d d', fun d d' => Datum_rel_iff_exists_H0_smul_dat_eq c d d', fun d g => ?_, fun d0 d => ?_⟩` and prove the remaining obligations. Rewrite using `[Datum_stab_eq_comap_H0_inf_stabilizer c d]`. Conclude with `Subgroup.mem_comap`. Unfold `_root_.Formalism.MainNotions.S.LocNG.Datum.wt _root_.Formalism.MainNotions.S.LocNG.volRel _root_.GlobalTheory.HL.invVol`.

Rewrite using `[Datum_stab_eq_comap_H0_inf_stabilizer c d, Datum_stab_eq_comap_H0_inf_stabilizer c d0, relIndex_comap_mulEquiv, relIndex_comap_mulEquiv, one_div_div]`.
-/
theorem _root_.GlobalTheory.HL.CoordDatum.transport : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    [MeasurableSpace E] (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V]
    (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ) (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k)
    (c : _root_.GlobalTheory.HL.Coord P S), Function.Injective c.dat ∧
    (∀ g ∈ P.UW0, ∀ d d', _root_.Formalism.MainNotions.S.LocNG.Datum.Moves g d d' ↔
      c.grp g • c.dat d = c.dat d') ∧
    (∀ d d', _root_.Formalism.MainNotions.S.LocNG.Datum.Rel d d' ↔
      ∃ h ∈ S.H0, h • c.dat d = c.dat d') ∧
    (∀ d g, g ∈ _root_.Formalism.MainNotions.S.LocNG.Datum.Stab d ↔ c.grp g ∈
      S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) ∧
    ∀ d0 d, _root_.Formalism.MainNotions.S.LocNG.Datum.wt d0 d = _root_.GlobalTheory.HL.invVol
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d0))
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r k P S c
  refine ⟨dat_injective c, fun g hg d d' => Datum_moves_iff_grp_smul_dat_eq c g hg d d',
    fun d d' => Datum_rel_iff_exists_H0_smul_dat_eq c d d', fun d g => ?_, fun d0 d => ?_⟩
  · rw [Datum_stab_eq_comap_H0_inf_stabilizer c d]
    exact Subgroup.mem_comap
  · unfold _root_.Formalism.MainNotions.S.LocNG.Datum.wt _root_.Formalism.MainNotions.S.LocNG.volRel _root_.GlobalTheory.HL.invVol
    rw [Datum_stab_eq_comap_H0_inf_stabilizer c d, Datum_stab_eq_comap_H0_inf_stabilizer c d0, relIndex_comap_mulEquiv, relIndex_comap_mulEquiv,
      one_div_div]

end GlobalTheory.HL.CoordDatum
