import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameCoordinatesTransportInnerLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLatticesStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.CoordTerm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

/- English proof (translation)
Unfold `Coord.lat`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h⟩`. Establish `: y = x` using `c.e.injective h`. Conclude with `this ▸ hy`.

Introduce `h`. Conclude with `⟨x, h, rfl⟩`.
-/
lemma mem_lat (Λ : Submodule M.L.O V) (x : V) : c.e x ∈ c.lat Λ ↔ x ∈ Λ := by
  unfold Coord.lat
  constructor
  · rintro ⟨y, hy, h⟩
    have : y = x := c.e.injective h
    exact this ▸ hy
  · intro h; exact ⟨x, h, rfl⟩

/- English proof (translation)
Simplify using `[Coord.grp]`.
-/
lemma grp_e (g : V ≃ₗ[E] V) (x : V) : c.grp g (c.e x) = c.e (g x) := by
  simp [Coord.grp]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `x`. Rewrite using `[← mem_lat c, h, mem_lat]`. Introduce and unpack `rfl`.

Both sides reduce to the same expression.
-/
lemma lat_inj {Λ Λ' : Submodule M.L.O V} : c.lat Λ = c.lat Λ' ↔ Λ = Λ' := by
  constructor
  · intro h; ext x; rw [← mem_lat c, h, mem_lat]
  · rintro rfl; rfl

/- English proof (translation)
Use extensionality with `y`. Take `⟨x, rfl⟩` from `c.e.surjective y`. Rewrite using `[mem_lat, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`.

Conclude with `⟨c.e z, (mem_lat c _ _).2 hz, grp_e c g z⟩`. Introduce and unpack `⟨w, hw, h⟩`. Take `⟨z, rfl⟩` from `c.e.surjective w`. Establish `h2 : c.e (g z) = c.e x` using `(grp_e c g z).symm.trans h`. Conclude with `⟨z, (mem_lat c _ _).1 hw, c.e.injective h2⟩`.
-/
lemma lat_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    c.lat (LocNG.img g Λ) = c.grp g • c.lat Λ := by
  ext y
  obtain ⟨x, rfl⟩ := c.e.surjective y
  rw [mem_lat, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨c.e z, (mem_lat c _ _).2 hz, grp_e c g z⟩
  · rintro ⟨w, hw, h⟩
    obtain ⟨z, rfl⟩ := c.e.surjective w
    have h2 : c.e (g z) = c.e x := (grp_e c g z).symm.trans h
    exact ⟨z, (mem_lat c _ _).1 hw, c.e.injective h2⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Unfold `HermSp.smulLat at h`. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨y, hy, rfl⟩ := hx`.

Conclude with `⟨y, hy, rfl⟩`. Consider the case `zero => exact ⟨0, Λ.zero_mem, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨u, hu, rfl⟩` from `hx`. Take `⟨v, hv, rfl⟩` from `hy`.

Conclude with `⟨u + v, Λ.add_mem hu hv, by simp⟩`. Consider the case `smul s x _ hx`. Take `⟨u, hu, rfl⟩` from `hx`. Conclude with `⟨s • u, Λ.smul_mem s hu, smul_comm _ _ _⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `Submodule.subset_span ⟨y, hy, rfl⟩`.
-/
lemma mem_smulLat (a : E) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ H.smulLat a Λ ↔ ∃ y ∈ Λ, x = a • y := by
  constructor
  · intro h
    unfold HermSp.smulLat at h
    induction h using Submodule.span_induction with
    | mem x hx => obtain ⟨y, hy, rfl⟩ := hx; exact ⟨y, hy, rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      exact ⟨u + v, Λ.add_mem hu hv, by simp⟩
    | smul s x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact ⟨s • u, Λ.smul_mem s hu, smul_comm _ _ _⟩
  · rintro ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

/- English proof (translation)
Rewrite using `[mem_smulLat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, h⟩`. Take `⟨z, rfl⟩` from `c.e.surjective w`. Conclude with `⟨z, (mem_lat c _ _).1 hw, c.e.injective (by rw [h, map_smul])⟩`.

Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨c.e z, (mem_lat c _ _).2 hz, by rw [map_smul]⟩`.
-/
lemma inTh_iff (Λ : Submodule M.L.O V) (x : V) :
    S.InTh (c.lat Λ) (c.e x) ↔ x ∈ H.smulLat (algebraMap F E S.th) Λ := by
  rw [mem_smulLat]
  constructor
  · rintro ⟨w, hw, h⟩
    obtain ⟨z, rfl⟩ := c.e.surjective w
    exact ⟨z, (mem_lat c _ _).1 hw, c.e.injective (by rw [h, map_smul])⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨c.e z, (mem_lat c _ _).2 hz, by rw [map_smul]⟩

/- English proof (translation)
Rewrite using `[H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]`.
-/
lemma h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

/- English proof (translation)
Unfold `HermSp.X`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩ x hx`. Rewrite using `[H.h_herm x]`. Establish `: H.h x (Fr.f a.castSucc) = 0`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, rfl⟩` from `hx`. Conclude with `Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last b).ne)`. Consider the case `zero => exact H.h_zero_left _`.

Consider the case `add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]`. Consider the case `smul s x _ hx => rw [H.h_smul_left, hx, mul_zero]`. Rewrite using `[this, map_zero]`.
-/
lemma X_le_perp (Fr : LocNG.FrameD H r) : H.X Fr.f ≤ H.perp (H.X Fr.f) := by
  unfold HermSp.X
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩ x hx
  rw [H.h_herm x]
  have : H.h x (Fr.f a.castSucc) = 0 := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last b).ne)
    | zero => exact H.h_zero_left _
    | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
    | smul s x _ hx => rw [H.h_smul_left, hx, mul_zero]
  rw [this, map_zero]

/- English proof (translation)
Unfold `HermSp.mkW`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Both sides reduce to the same expression.
-/
lemma mkW_eq (f : Fin (r + 1) → V) (x y : ↥(H.perp (H.X f))) :
    H.mkW f x = H.mkW f y ↔ (x : V) - y ∈ H.X f := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  rfl

/- English proof (translation)
The claim follows from `Submodule.mkQ_surjective _`.
-/
lemma mkW_surj (f : Fin (r + 1) → V) : Function.Surjective (H.mkW f) :=
  Submodule.mkQ_surjective _

/- English proof (translation)
Take `⟨v, rfl⟩` from `c.e.surjective y`. Unfold `Coord.inn`. Rewrite using `[mem_lat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Conclude with `⟨x, rfl, hx⟩`. Introduce and unpack `⟨x, h, hx⟩`. Conclude with `⟨x, hx, (c.e.injective h).symm⟩`.
-/
lemma mem_inn (f : Fin (r + 1) → V) (L : Submodule M.L.O (H.Wb f)) (y : S.V) :
    y ∈ c.inn f L ↔ ∃ x : ↥(H.perp (H.X f)), y = c.e x ∧ H.mkW f x ∈ L := by
  obtain ⟨v, rfl⟩ := c.e.surjective y
  unfold Coord.inn
  rw [mem_lat]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, rfl, hx⟩
  · rintro ⟨x, h, hx⟩
    exact ⟨x, hx, (c.e.injective h).symm⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `hn`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hA, hB⟩`. Take `⟨z, hz, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy`. Establish `hzA : z ∈ A` using `(h1 z).1 hA`.

Use `⟨z, hz, hzA, ?_⟩` and prove the remaining obligations. Use `B.sub_mem hB (h2 z hzA)` as an intermediate fact. Establish `e : n • z - x - (n z - z) = z - x`. Express the relevant statement in the definitionally equal form `n z - x - (n z - z) = z - x`. Normalize the expressions using the abelian group laws.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Introduce and unpack `⟨z, hz, hA, hB⟩`. Use `⟨n • z, Submodule.smul_mem_pointwise_smul _ _ _ hz, (h1 z).2 hA, ?_⟩` and prove the remaining obligations. Use `B.add_mem hB (h2 z hA)` as an intermediate fact. Establish `e : z - x + (n z - z) = n • z - x`.

Express the relevant statement in the definitionally equal form `_ = n z - x`. Normalize the expressions using the abelian group laws. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
lemma trace_smul {A B : Submodule E S.V} {n : S.GLV} (hn : n ∈ unipOn A B)
    (Λ : Submodule M.L.O S.V) (x : S.V) :
    (∃ y ∈ n • Λ, y ∈ A ∧ y - x ∈ B) ↔ ∃ y ∈ Λ, y ∈ A ∧ y - x ∈ B := by
  obtain ⟨h1, h2⟩ := hn
  constructor
  · rintro ⟨y, hy, hA, hB⟩
    obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    have hzA : z ∈ A := (h1 z).1 hA
    refine ⟨z, hz, hzA, ?_⟩
    have := B.sub_mem hB (h2 z hzA)
    have e : n • z - x - (n z - z) = z - x := by
      change n z - x - (n z - z) = z - x
      abel
    rwa [e] at this
  · rintro ⟨z, hz, hA, hB⟩
    refine ⟨n • z, Submodule.smul_mem_pointwise_smul _ _ _ hz, (h1 z).2 hA, ?_⟩
    have := B.add_mem hB (h2 z hA)
    have e : z - x + (n z - z) = n • z - x := by
      change _ = n z - x
      abel
    rwa [e] at this

/- English proof (translation)
Take `⟨hth, -, -, -, -, hX, hX', hp, hp'⟩` from `GlobalTheory.HL.CoordUnip.transport M hM H r k P S c`. Establish `hq : S.th = (g.q : F)` using `by rw [← hth, LocNG.theta, hg]`. Take `⟨p', p⟩` from `p`. Take `⟨p', rfl⟩` from `c.e.surjective p'`. Take `⟨p, rfl⟩` from `c.e.surjective p`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩`. Take `⟨y', rfl⟩` from `c.e.surjective y'`. Take `⟨y, rfl⟩` from `c.e.surjective y`. Simplify using `only at h3 h4`.

Rewrite `h3` using `[← map_sub, ← hX']`. Rewrite `h4` using `[← map_sub, ← hX]`. Rewrite `h1` using `[← hp']`. Rewrite `h2` using `[← hp]`. Rewrite `h5` using `[← map_sub, inTh_iff, hq]`.

Establish `k1 : p' ∈ H.perp (H.X P.B.f)`. Use `Submodule.sub_mem _ h1 (X_le_perp P.B h3)` as an intermediate fact. Simplify using `using this`. Establish `k2 : p ∈ H.perp (H.X P.A.f)`. Use `Submodule.sub_mem _ h2 (X_le_perp P.A h4)` as an intermediate fact.

Simplify using `using this`. Use `⟨⟨p', k1⟩, ⟨p, k2⟩, rfl, ⟨y', h1⟩, ⟨y, h2⟩, (mem_lat c _ _).1 hy', (mem_lat c _ _).1 hy, ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.neg_mem _ h5` as an intermediate fact. Simplify using `using this`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Conclude with `((mkW_eq P.B.f ⟨y', h1⟩ ⟨p', k1⟩).2 h3).symm`. Conclude with `((mkW_eq P.A.f ⟨y, h2⟩ ⟨p, k2⟩).2 h4).symm`. Introduce and unpack `⟨x', x, e, y', y, hy', hy, h5, h⟩`. Rewrite using `[e]`. Establish `e1 : H.mkW P.B.f y' = H.mkW P.B.f x'` using `(congrArg Prod.fst h).symm`.

Establish `e2 : H.mkW P.A.f y = H.mkW P.A.f x` using `(congrArg Prod.snd h).symm`. Rewrite `e1`, `e2` using `[mkW_eq]`. Use `⟨c.e y', (mem_lat c _ _).2 hy', c.e y, (mem_lat c _ _).2 hy, (hp' _).1 y'.2, (hp _).1 y.2, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← map_sub, ← hX']`.

Conclude with `e1`. Simplify using `only`. Rewrite using `[← map_sub, ← hX]`. Conclude with `e2`. Rewrite using `[← map_sub, inTh_iff, hq]`.

Use `Submodule.neg_mem _ h5` as an intermediate fact. Simplify using `using this`.
-/
lemma mem_graphOf (hM : M.OK) (g : SplitG M.L) (hg : M.split = some g) (Λ : Submodule M.L.O V) (T T' : F)
    (p : S.V × S.V) :
    p ∈ S.graphOf (c.lat Λ) ↔ ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))),
      p = (c.e x', c.e x) ∧
        (H.mkW P.B.f x', H.mkW P.A.f x) ∈ H.iotaGraph g ⟨Λ, P.A.f, P.B.f, T, T'⟩ := by
  obtain ⟨hth, -, -, -, -, hX, hX', hp, hp'⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hq : S.th = (g.q : F) := by rw [← hth, LocNG.theta, hg]
  obtain ⟨p', p⟩ := p
  obtain ⟨p', rfl⟩ := c.e.surjective p'
  obtain ⟨p, rfl⟩ := c.e.surjective p
  constructor
  · rintro ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩
    obtain ⟨y', rfl⟩ := c.e.surjective y'
    obtain ⟨y, rfl⟩ := c.e.surjective y
    dsimp only at h3 h4
    rw [← map_sub, ← hX'] at h3
    rw [← map_sub, ← hX] at h4
    rw [← hp'] at h1
    rw [← hp] at h2
    rw [← map_sub, inTh_iff, hq] at h5
    have k1 : p' ∈ H.perp (H.X P.B.f) := by
      have := Submodule.sub_mem _ h1 (X_le_perp P.B h3)
      simpa using this
    have k2 : p ∈ H.perp (H.X P.A.f) := by
      have := Submodule.sub_mem _ h2 (X_le_perp P.A h4)
      simpa using this
    refine ⟨⟨p', k1⟩, ⟨p, k2⟩, rfl, ⟨y', h1⟩, ⟨y, h2⟩, (mem_lat c _ _).1 hy', (mem_lat c _ _).1 hy, ?_, ?_⟩
    · have := Submodule.neg_mem _ h5
      simpa using this
    · refine Prod.ext ?_ ?_
      · exact ((mkW_eq P.B.f ⟨y', h1⟩ ⟨p', k1⟩).2 h3).symm
      · exact ((mkW_eq P.A.f ⟨y, h2⟩ ⟨p, k2⟩).2 h4).symm
  · rintro ⟨x', x, e, y', y, hy', hy, h5, h⟩
    rw [e]
    have e1 : H.mkW P.B.f y' = H.mkW P.B.f x' := (congrArg Prod.fst h).symm
    have e2 : H.mkW P.A.f y = H.mkW P.A.f x := (congrArg Prod.snd h).symm
    rw [mkW_eq] at e1 e2
    refine ⟨c.e y', (mem_lat c _ _).2 hy', c.e y, (mem_lat c _ _).2 hy, (hp' _).1 y'.2, (hp _).1 y.2, ?_, ?_, ?_⟩
    · dsimp only; rw [← map_sub, ← hX']; exact e1
    · dsimp only; rw [← map_sub, ← hX]; exact e2
    · rw [← map_sub, inTh_iff, hq]
      have := Submodule.neg_mem _ h5
      simpa using this

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c d n n' Λ`. Use `letI := hM.loc`. Use `haveI := hM.char0`. Take `⟨hth, hN, hN', -⟩` from `GlobalTheory.HL.CoordUnip.transport M hM H r k P S c`. Take `⟨-, iA, -, sA⟩` from `GlobalTheory.T.hermitianFrameCoordinates_transport_innerLattices M hM H r k P S c`.

Take `⟨-, iB, -, sB⟩` from `GlobalTheory.T.framePairCoordinates_transport_innerLattices M hM H r k P S c`. Establish `hA` using `(iA d.L).1 d.hL`. Establish `hB` using `(iB d.L').1 d.hL'`. Establish `eA : Λ = LocNG.img n (P.A.LamStd d.L) ↔ c.lat Λ = c.grp n • S.stdLat S.f S.es (c.inn P.A.f d.L)`. Rewrite using `[← sA, ← lat_img, lat_inj]`.

Establish `eB : Λ = LocNG.img n' (P.B.LamStd d.L') ↔ c.lat Λ = c.grp n' • S.stdLat S.f' S.es' (c.inn P.B.f d.L')`. Rewrite using `[← sB, ← lat_img, lat_inj]`. Establish `ed : ∀ b, c.grp n' (S.f' b) - c.grp n (S.f b) = c.e (n' (P.B.f b) - n (P.A.f b))`. Introduce `b`. Rewrite using `[c.f_eq, c.f'_eq, grp_e, grp_e, map_sub]`.

Establish `key : n ∈ P.A.N → n' ∈ P.B.N → Λ = LocNG.img n (P.A.LamStd d.L) → Λ = LocNG.img n' (P.B.LamStd d.L') → ((∀ g, M.split = some g → H.Admissible g (⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ : Term V M r) ∧ H.iotaGraph g ⟨Λ, P.A.f, P.B.f, P.A.T, P.B.T⟩ = d.io) ↔ …`. Introduce `hn hn' h1 h2`. Rewrite `hn` using `[hN]`. Rewrite `hn'` using `[hN']`. Rewrite `h1` using `[eA]`.

Rewrite `h2` using `[eB]`. Consider the cases of `hs : M.split with`. Consider the case `none`. Establish `h0 : S.th = 1` using `by rw [← hth, LocNG.theta, hs]`. Establish `hI : ∀ x, S.InTh (c.lat Λ) x ↔ x ∈ c.lat Λ`.

Introduce `x`. Simplify using `[Frames.InTh, h0]`. Take `⟨-, a2, a3⟩` from `GlobalTheory.HL.StdLat.stdLat_spec M.L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA`. Take `⟨-, b2, b3⟩` from `GlobalTheory.HL.StdLat.stdLat_spec M.L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hB`. Use `iff_of_true (by simp) ⟨fun b => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hI]`. Use `Submodule.sub_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ ((b2 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)).1`. Rewrite using `[h1]`.

Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ ((a2 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)).1`. Establish `tA` using `fun x => (a3 x).trans (trace_smul hn.2 _ x).symm`. Establish `tB` using `fun x => (b3 x).trans (trace_smul hn'.2 _ x).symm`. Rewrite `tA` using `[← h1]`. Rewrite `tB` using `[← h2]`.

Use extensionality with `p`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x', x, rfl, ⟨-, u', u⟩ | u⟩`. Take `⟨y, y1, y2, y3⟩` from `(tA _).1 ((mem_inn c _ _ _).2 ⟨x, rfl, u⟩)`. Take `⟨z, z1, z2, z3⟩` from `(tB _).1 ((mem_inn c _ _ _).2 ⟨x', rfl, u'⟩)`.

Conclude with `⟨z, z1, y, y1, z2, y2, z3, y3, (hI _).2 (Submodule.sub_mem _ z1 y1)⟩`. Rewrite `u` using `[d.io_L hs]`. Conclude with `u.elim`. Introduce and unpack `⟨z, z1, y, y1, z2, y2, z3, y3, -⟩`. Take `⟨x, e, u⟩` from `(mem_inn c _ _ _).1 ((tA _).2 ⟨y, y1, y2, y3⟩)`.

Take `⟨x', e', u'⟩` from `(mem_inn c _ _ _).1 ((tB _).2 ⟨z, z1, z2, z3⟩)`. Conclude with `⟨x', x, Prod.ext e' e, Or.inl ⟨hs, u', u⟩⟩`. Consider the case `some g`. Establish `hq : S.th = (g.q : F)` using `by rw [← hth, LocNG.theta, hs]`. Establish `hd : ∀ p, p ∈ (c.dat d).2.2 ↔ ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))), p = (c.e x', c.e x) ∧ (H.mkW P.B.f x', H.mkW P.A.f x) ∈ d.io`.

Introduce `p`. Simplify using `[Coord.dat, hs]`. Simplify using `only [Option.some.injEq, forall_eq']`. Use `and_congr ?_ ?_` and prove the remaining obligations. Use `forall_congr' fun b => ?_` and prove the remaining obligations.

Rewrite using `[ed, inTh_iff, hq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `p`. Rewrite using `[hd, mem_graphOf c hM g hs Λ P.A.T P.B.T, h]`.

Introduce `h`. Use extensionality with `⟨w', w⟩`. Take `⟨x', rfl⟩` from `mkW_surj P.B.f w'`. Take `⟨x, rfl⟩` from `mkW_surj P.A.f w`. Establish `hh : (c.e x', c.e x) ∈ (c.dat d).2.2 ↔ (c.e x', c.e x) ∈ S.graphOf (c.lat Λ)` using `by rw [h]`.

Rewrite `hh` using `[hd, mem_graphOf c hM g hs Λ P.A.T P.B.T]`. Establish `inj : ∀ (Z : Set (H.Wb P.B.f × H.Wb P.A.f)), (∃ (y' : ↥(H.perp (H.X P.B.f))) (y : ↥(H.perp (H.X P.A.f))), (c.e x', c.e x) = (c.e y', c.e y) ∧ (H.mkW P.B.f y', H.mkW P.A.f y) ∈ Z) ↔ (H.mkW P.B.f x', H.mkW P.A.f x) ∈ Z`. Introduce `Z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y', y, e, u⟩`.

Establish `e1 : x' = y'` using `Subtype.ext (c.e.injective (congrArg Prod.fst e))`. Establish `e2 : x = y` using `Subtype.ext (c.e.injective (congrArg Prod.snd e))`. Rewrite using `[e1, e2]`. Conclude with `u`. Introduce `u`.

Conclude with `⟨x', x, rfl, u⟩`. Conclude with `((inj _).symm.trans (hh.symm.trans (inj _)))`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨-, -, -, -, hG⟩, hn, hn', h1, h2⟩`. Take `⟨k1, k2⟩` from `(key hn hn' h1 h2).1 hG`.

Conclude with `⟨hA, hB, (hN n).1 hn, (hN' n').1 hn', eA.1 h1, eB.1 h2, k1, k2⟩`. Introduce and unpack `⟨-, -, hn, hn', h1, h2, k1, k2⟩`. Establish `hn` using `(hN n).2 hn`. Establish `hn'` using `(hN' n').2 hn'`. Establish `h1` using `eA.2 h1`.

Establish `h2` using `eB.2 h2`. Conclude with `⟨⟨rfl, rfl, ⟨n, hn, rfl, h1⟩, ⟨n', hn', rfl, h2⟩, (key hn hn' h1 h2).2 ⟨k1, k2⟩⟩, hn, hn', h1, h2⟩`.
-/
theorem isTermW_iff : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (d : LocNG.Datum P) (n n' : V ≃ₗ[E] V) (Λ : Submodule M.L.O V), LocNG.IsTermOver P d ⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ ∧ n ∈ P.A.N ∧ n' ∈ P.B.N ∧ Λ = LocNG.img n (P.A.LamStd d.L) ∧ Λ = LocNG.img n' (P.B.LamStd d.L') ↔ S.IsTermW (c.dat d) (c.lat Λ) (c.grp n) (c.grp n') := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c d n n' Λ
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨hth, hN, hN', -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  obtain ⟨-, iA, -, sA⟩ := GlobalTheory.T.hermitianFrameCoordinates_transport_innerLattices M hM H r k P S c
  obtain ⟨-, iB, -, sB⟩ := GlobalTheory.T.framePairCoordinates_transport_innerLattices M hM H r k P S c
  have hA := (iA d.L).1 d.hL
  have hB := (iB d.L').1 d.hL'
  have eA : Λ = LocNG.img n (P.A.LamStd d.L) ↔
      c.lat Λ = c.grp n • S.stdLat S.f S.es (c.inn P.A.f d.L) := by
    rw [← sA, ← lat_img, lat_inj]
  have eB : Λ = LocNG.img n' (P.B.LamStd d.L') ↔
      c.lat Λ = c.grp n' • S.stdLat S.f' S.es' (c.inn P.B.f d.L') := by
    rw [← sB, ← lat_img, lat_inj]
  have ed : ∀ b, c.grp n' (S.f' b) - c.grp n (S.f b) = c.e (n' (P.B.f b) - n (P.A.f b)) := by
    intro b; rw [c.f_eq, c.f'_eq, grp_e, grp_e, map_sub]
  have key : n ∈ P.A.N → n' ∈ P.B.N → Λ = LocNG.img n (P.A.LamStd d.L) →
      Λ = LocNG.img n' (P.B.LamStd d.L') →
      ((∀ g, M.split = some g →
        H.Admissible g (⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ : Term V M r) ∧
        H.iotaGraph g ⟨Λ, P.A.f, P.B.f, P.A.T, P.B.T⟩ = d.io) ↔
      ((∀ b, S.InTh (c.lat Λ) (c.grp n' (S.f' b) - c.grp n (S.f b))) ∧
        (c.dat d).2.2 = S.graphOf (c.lat Λ))) := by
    intro hn hn' h1 h2
    rw [hN] at hn
    rw [hN'] at hn'
    rw [eA] at h1
    rw [eB] at h2
    cases hs : M.split with
    | none =>
      have h0 : S.th = 1 := by rw [← hth, LocNG.theta, hs]
      have hI : ∀ x, S.InTh (c.lat Λ) x ↔ x ∈ c.lat Λ := by
        intro x; simp [Frames.InTh, h0]
      obtain ⟨-, a2, a3⟩ := GlobalTheory.HL.StdLat.stdLat_spec M.L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA
      obtain ⟨-, b2, b3⟩ := GlobalTheory.HL.StdLat.stdLat_spec M.L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hB
      refine iff_of_true (by simp) ⟨fun b => ?_, ?_⟩
      · rw [hI]
        refine Submodule.sub_mem _ ?_ ?_
        · rw [h2]
          exact Submodule.smul_mem_pointwise_smul _ _ _
            ((b2 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
        · rw [h1]
          exact Submodule.smul_mem_pointwise_smul _ _ _
            ((a2 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
      · have tA := fun x => (a3 x).trans (trace_smul hn.2 _ x).symm
        have tB := fun x => (b3 x).trans (trace_smul hn'.2 _ x).symm
        rw [← h1] at tA
        rw [← h2] at tB
        ext p
        constructor
        · rintro ⟨x', x, rfl, ⟨-, u', u⟩ | u⟩
          · obtain ⟨y, y1, y2, y3⟩ := (tA _).1 ((mem_inn c _ _ _).2 ⟨x, rfl, u⟩)
            obtain ⟨z, z1, z2, z3⟩ := (tB _).1 ((mem_inn c _ _ _).2 ⟨x', rfl, u'⟩)
            exact ⟨z, z1, y, y1, z2, y2, z3, y3, (hI _).2 (Submodule.sub_mem _ z1 y1)⟩
          · rw [d.io_L hs] at u; exact u.elim
        · rintro ⟨z, z1, y, y1, z2, y2, z3, y3, -⟩
          obtain ⟨x, e, u⟩ := (mem_inn c _ _ _).1 ((tA _).2 ⟨y, y1, y2, y3⟩)
          obtain ⟨x', e', u'⟩ := (mem_inn c _ _ _).1 ((tB _).2 ⟨z, z1, z2, z3⟩)
          exact ⟨x', x, Prod.ext e' e, Or.inl ⟨hs, u', u⟩⟩
    | some g =>
      have hq : S.th = (g.q : F) := by rw [← hth, LocNG.theta, hs]
      have hd : ∀ p, p ∈ (c.dat d).2.2 ↔ ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))),
          p = (c.e x', c.e x) ∧ (H.mkW P.B.f x', H.mkW P.A.f x) ∈ d.io := by
        intro p; simp [Coord.dat, hs]
      simp only [Option.some.injEq, forall_eq']
      refine and_congr ?_ ?_
      · refine forall_congr' fun b => ?_
        rw [ed, inTh_iff, hq]
      · constructor
        · intro h
          ext p
          rw [hd, mem_graphOf c hM g hs Λ P.A.T P.B.T, h]
        · intro h
          ext ⟨w', w⟩
          obtain ⟨x', rfl⟩ := mkW_surj P.B.f w'
          obtain ⟨x, rfl⟩ := mkW_surj P.A.f w
          have hh : (c.e x', c.e x) ∈ (c.dat d).2.2 ↔ (c.e x', c.e x) ∈ S.graphOf (c.lat Λ) := by rw [h]
          rw [hd, mem_graphOf c hM g hs Λ P.A.T P.B.T] at hh
          have inj : ∀ (Z : Set (H.Wb P.B.f × H.Wb P.A.f)),
              (∃ (y' : ↥(H.perp (H.X P.B.f))) (y : ↥(H.perp (H.X P.A.f))),
                (c.e x', c.e x) = (c.e y', c.e y) ∧ (H.mkW P.B.f y', H.mkW P.A.f y) ∈ Z) ↔
              (H.mkW P.B.f x', H.mkW P.A.f x) ∈ Z := by
            intro Z
            constructor
            · rintro ⟨y', y, e, u⟩
              have e1 : x' = y' := Subtype.ext (c.e.injective (congrArg Prod.fst e))
              have e2 : x = y := Subtype.ext (c.e.injective (congrArg Prod.snd e))
              rw [e1, e2]; exact u
            · intro u; exact ⟨x', x, rfl, u⟩
          exact ((inj _).symm.trans (hh.symm.trans (inj _)))
  constructor
  · rintro ⟨⟨-, -, -, -, hG⟩, hn, hn', h1, h2⟩
    obtain ⟨k1, k2⟩ := (key hn hn' h1 h2).1 hG
    exact ⟨hA, hB, (hN n).1 hn, (hN' n').1 hn', eA.1 h1, eB.1 h2, k1, k2⟩
  · rintro ⟨-, -, hn, hn', h1, h2, k1, k2⟩
    have hn := (hN n).2 hn
    have hn' := (hN' n').2 hn'
    have h1 := eA.2 h1
    have h2 := eB.2 h2
    exact ⟨⟨rfl, rfl, ⟨n, hn, rfl, h1⟩, ⟨n', hn', rfl, h2⟩, (key hn hn' h1 h2).2 ⟨k1, k2⟩⟩, hn, hn', h1, h2⟩

end GlobalTheory.HL.CoordTerm
