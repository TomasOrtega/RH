import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumOfTermReadOnLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovePreservesFrameLatticeLevels
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMoveCharacterNeOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespond
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.GenericTerm

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k}

/- English proof (translation)
Take `⟨hfg, hsp, hd⟩` from `h`. Establish `e : ∀ x y, hf M.L S.Hm (c.e y) (c.e x) = H.h y x` using `fun x y => c.h_eq y x`. Use `⟨⟨hfg.map _, ?_⟩, fun y => ?_⟩` and prove the remaining obligations. Establish `h1 : ((c.lat Λ : Submodule M.L.O S.V) : Set S.V) = (c.e : V →ₗ[E] S.V) '' (Λ : Set V)`. Rewrite using `[Coord.lat, Submodule.map_coe]`.

Both sides reduce to the same expression. Rewrite using `[h1, Submodule.span_image, hsp, Submodule.map_top]`. Conclude with `LinearEquiv.range c.e`. Take `⟨z, rfl⟩` from `c.e.surjective y`. Rewrite using `[CoordTerm.mem_lat, hd z]`.

Prove the components needed by the constructor for the conclusion. Introduce `h w hw`. Establish `h2` using `h (c.e w) ((CoordTerm.mem_lat c Λ w).2 hw)`. Rewrite `h2` using `[e]`. Rewrite using `[H.h_herm w z]`.

Conclude with `GlobalTheory.LocOver.TermLat.cj_mem h2`. Introduce `h x hx`. Take `⟨w, rfl⟩` from `c.e.surjective x`. Rewrite using `[e, H.h_herm z w]`. Conclude with `GlobalTheory.LocOver.TermLat.cj_mem (h w ((CoordTerm.mem_lat c Λ w).1 hx))`.
-/
theorem isSD_lat (c : Coord P S) (Λ : Submodule M.L.O V) (h : H.IsSelfDual Λ) :
    IsSD M.L S.Hm (c.lat Λ) := by
  obtain ⟨hfg, hsp, hd⟩ := h
  have e : ∀ x y, hf M.L S.Hm (c.e y) (c.e x) = H.h y x := fun x y => c.h_eq y x
  refine ⟨⟨hfg.map _, ?_⟩, fun y => ?_⟩
  · have h1 : ((c.lat Λ : Submodule M.L.O S.V) : Set S.V) = (c.e : V →ₗ[E] S.V) '' (Λ : Set V) := by
      rw [Coord.lat, Submodule.map_coe]; rfl
    rw [h1, Submodule.span_image, hsp, Submodule.map_top]
    exact LinearEquiv.range c.e
  · obtain ⟨z, rfl⟩ := c.e.surjective y
    rw [CoordTerm.mem_lat, hd z]
    constructor
    · intro h w hw
      have h2 := h (c.e w) ((CoordTerm.mem_lat c Λ w).2 hw)
      rw [e] at h2
      rw [H.h_herm w z]
      exact GlobalTheory.LocOver.TermLat.cj_mem h2
    · intro h x hx
      obtain ⟨w, rfl⟩ := c.e.surjective x
      rw [e, H.h_herm z w]
      exact GlobalTheory.LocOver.TermLat.cj_mem (h w ((CoordTerm.mem_lat c Λ w).1 hx))

/- English proof (translation)
Break down `hs : M.split with _ | g` into its components or cases. Establish `h1 : LocNG.theta M = 1` using `by simp [LocNG.theta, hs]`. Rewrite using `[h1, map_one]`. Conclude with `M.L.O.one_mem`. Establish `h1 : LocNG.theta M = (g.q : F)` using `by simp [LocNG.theta, hs]`.

Rewrite using `[h1, M.L.O_def]`. Conclude with `(isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := g.q)).algebraMap`.
-/
theorem theta_mem (M : Model F E) : algebraMap F E (LocNG.theta M) ∈ M.L.O := by
  rcases hs : M.split with _ | g
  · have h1 : LocNG.theta M = 1 := by simp [LocNG.theta, hs]
    rw [h1, map_one]
    exact M.L.O.one_mem
  · have h1 : LocNG.theta M = (g.q : F) := by simp [LocNG.theta, hs]
    rw [h1, M.L.O_def]
    exact (isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := g.q)).algebraMap

/- English proof (translation)
Take `⟨al, al', e, hal⟩` from `(MoveSame.mem_Mof S g g' x).1 hx`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨α, hα⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 h`. Establish `h2 : ∑ i, al i • g i + ∑ i, al' i • g' i = ∑ i, α i • g i + ∑ i, (0 : Fin (r + 1) → E) i • g' i`.

Rewrite using `[← e, hα]`. Simplify using the standard rewrite rules. Take `⟨h3, h4⟩` from `MoveChar.uniq S hli h2`. Substitute `h3 h4` using the available equality. Rewrite using `[e]`.

Simplify using `only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]`. Conclude with `FrameLift.sum_mem_O S al g (fun i => by simpa using (hal i).2) (fun i => Submodule.subset_span ⟨i, rfl⟩)`. Introduce `h`. Take `⟨α, hα⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 h`. Establish `h2 : ∑ i, al i • g i + ∑ i, al' i • g' i = ∑ i, (0 : Fin (r + 1) → E) i • g i + ∑ i, α i • g' i`.

Rewrite using `[← e, hα]`. Simplify using the standard rewrite rules. Take `⟨h3, h4⟩` from `MoveChar.uniq S hli h2`. Substitute `h3 h4` using the available equality. Rewrite using `[e]`.

Simplify using `only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]`. Conclude with `FrameLift.sum_mem_O S al' g' (fun i => by simpa using (hal i).2) (fun i => Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem mem_span_of_Mof (S : Frames M.L r k) {g g' : Fin (r + 1) → S.V}
    (hli : LinearIndependent E (Sum.elim g g')) {x : S.V} (hx : x ∈ S.Mof g g') :
    (x ∈ Submodule.span E (Set.range g) → x ∈ Submodule.span M.L.O (Set.range g)) ∧
      (x ∈ Submodule.span E (Set.range g') → x ∈ Submodule.span M.L.O (Set.range g')) := by
  obtain ⟨al, al', e, hal⟩ := (MoveSame.mem_Mof S g g' x).1 hx
  constructor
  · intro h
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 h
    have h2 : ∑ i, al i • g i + ∑ i, al' i • g' i =
        ∑ i, α i • g i + ∑ i, (0 : Fin (r + 1) → E) i • g' i := by
      rw [← e, hα]; simp
    obtain ⟨h3, h4⟩ := MoveChar.uniq S hli h2
    subst h3 h4
    rw [e]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    exact FrameLift.sum_mem_O S al g (fun i => by simpa using (hal i).2)
      (fun i => Submodule.subset_span ⟨i, rfl⟩)
  · intro h
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 h
    have h2 : ∑ i, al i • g i + ∑ i, al' i • g' i =
        ∑ i, (0 : Fin (r + 1) → E) i • g i + ∑ i, α i • g' i := by
      rw [← e, hα]; simp
    obtain ⟨h3, h4⟩ := MoveChar.uniq S hli h2
    subst h3 h4
    rw [e]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
    exact FrameLift.sum_mem_O S al' g' (fun i => by simpa using (hal i).2)
      (fun i => Submodule.subset_span ⟨i, rfl⟩)

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP f f' hf hf' Λ`. Use `letI := hM.loc`. Use `haveI := hM.char0`. Take `⟨S, ⟨c⟩⟩` from `CoordExist.exists_coord M hM H r k P hrk hP`. Take `⟨hth, hNA, hNB, -, -, -, -, -, -⟩` from `CoordUnip.transport M hM H r k P S c`.

Establish `hTL` using `GlobalTheory.LocOver.TermLat.datum_of_lattice M hM H r k P hrk hP`. Establish `hθ : LocNG.theta M ≠ 0` using `by rw [hth]; exact CoordTermWt.th_ne S`. Use `⟨⟨fun hL => ?_, fun hR => ?_⟩, fun d d' hd hd' => ?_⟩` and prove the remaining obligations. Use `rotate_left`. Take `⟨d, hd, hbb⟩` from `hR`.

Take `⟨hT, -, -⟩` from `hTL.1 d _ hd`. Take `⟨hsd, hfr, hfr', -, -, hadm⟩` from `hT`. Use `⟨hsd, hsd.1, ?_, hbb⟩` and prove the remaining obligations. Use `(CoordTermWt.fam_mem (H := H) _ Λ).2 ⟨hfr.1.1, fun b => ?_⟩` and prove the remaining obligations. Break down `hs : M.split with _ | g` into its components or cases.

Establish `h1 : LocNG.theta M = 1` using `by simp [LocNG.theta, hs]`. Rewrite using `[h1, inv_one, map_one, one_smul]`. Conclude with `Λ.sub_mem (hfr'.1.1 b) (hfr.1.1 b)`. Establish `h1 : LocNG.theta M = (g.q : F)` using `by simp [LocNG.theta, hs]`. Take `⟨y, hy, e⟩` from `(CoordTerm.mem_smulLat (H := H) _ Λ _).1 ((hadm g hs).2.2 b)`.

Use `show algebraMap F E (LocNG.theta M)⁻¹ • (f' b - f b) ∈ Λ`. Rewrite using `[show f' b - f b = _ from e, smul_smul, ← map_mul, ← h1, inv_mul_cancel₀ hθ, map_one, one_smul]`. Conclude with `hy`. Conclude with `hTL.2 d d' _ _ hd hd' rfl rfl (fun _ _ => rfl)`. Take `⟨hsd, -, hmm, hbb⟩` from `hL`.

Take `⟨n0, hn0, rfl⟩` from `hf`. Take `⟨n0', hn0', rfl⟩` from `hf'`. Establish `hg : ∀ a (j : Fin r), hf M.L S.Hm (S.f a) (S.f j.castSucc) = 0` using `fun a j => by`. Simplify using `[S.gram, Fin.castSucc_ne_last]`. Establish `hg' : ∀ a (j : Fin r), hf M.L S.Hm (S.f' a) (S.f' j.castSucc) = 0` using `fun a j => by`.

Simplify using `[S.gram', Fin.castSucc_ne_last]`. Establish `hN : c.grp n0 ∈ S.N` using `(hNA n0).1 hn0`. Establish `hN' : c.grp n0' ∈ S.N'` using `(hNB n0').1 hn0'`. Establish `hNf : ∀ b, c.grp n0 (S.f b) = c.e (n0 (P.A.f b))` using `fun b => by rw [c.f_eq, CoordTerm.grp_e]`. Establish `hNf' : ∀ b, c.grp n0' (S.f' b) = c.e (n0' (P.B.f b))` using `fun b => by`.

Rewrite using `[c.f'_eq, CoordTerm.grp_e]`. Use `set t : Term V M r := ⟨Λ, fun b => n0 (P.A.f b), fun b => n0' (P.B.f b), P.A.T, P.B.T⟩ with ht`. Take `⟨hfm, hdm⟩` from `(CoordTermWt.fam_mem (H := H) t Λ).1 hmm`. Establish `hfm' : ∀ b, n0' (P.B.f b) ∈ Λ` using `fun b => by`. Establish `h1 : n0' (P.B.f b) = n0 (P.A.f b) + algebraMap F E (LocNG.theta M) • (algebraMap F E (LocNG.theta M)⁻¹ • (t.f' b - t.f b))`.

Rewrite using `[smul_smul, ← map_mul, mul_inv_cancel₀ hθ, map_one, one_smul]`. Simplify using `[ht]`. Rewrite using `[h1]`. Conclude with `Λ.add_mem (hfm b) (Λ.smul_mem (⟨_, theta_mem M⟩ : M.L.O) (hdm b))`. Establish `hli` using `MoveSame.indep S hN hN'`.

Establish `hsdc` using `isSD_lat c Λ hsd`. Establish `hMc : ∀ y ∈ Λ, y ∈ Submodule.span E (Set.range (H.MMfam t)) → c.e y ∈ S.Mof (fun b => c.grp n0 (S.f b)) (fun b => c.grp n0' (S.f' b))`. Introduce `y hy hyE`. Establish `hyO : y ∈ Submodule.span M.L.O (Set.range (H.MMfam t))`. Assume the negation of the conclusion as `h`.

Conclude with `hbb ⟨y, hy, hyE, h⟩`. Establish `e1 : (fun b => c.grp n0 (S.f b)) = fun b => c.e (t.f b)` using `funext hNf`. Establish `e2 : (fun b => c.grp n0' (S.f' b)) = fun b => c.e (t.f' b)` using `funext hNf'`. Rewrite using `[e1, e2, ← CoordTermWt.lat_span c t]`. Conclude with `(CoordTerm.mem_lat c _ y).2 hyO`.

Establish `hfE` using `((CoordTermWt.fam_mem (H := H) t (Submodule.span E (Set.range (H.MMfam t)))).1 (fun i => Submodule.subset_span ⟨i, rfl⟩))`. Establish `htr : ∀ x, (x ∈ c.lat Λ ∧ x ∈ S.spanTo S.f (r + 1)) ↔ x ∈ Submodule.span M.L.O (Set.range fun b => c.grp n0 (S.f b))`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hxs⟩`.

Establish `hx' : (c.grp n0).symm x ∈ S.spanTo S.f (r + 1)` using `(TermBasic.map_mem_iff hg hN (r + 1) _).1 (by simpa using hxs)`. Rewrite `hx'` using `[TermBasic.spanTo_top]`. Take `⟨α, hα⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hx'`. Establish `hxα : x = ∑ i, α i • c.grp n0 (S.f i)`. Use `congrArg (c.grp n0) hα` as an intermediate fact.

Simplify `this.symm` using `[map_sum, map_smul]`. Take `⟨y, rfl⟩` from `c.e.surjective x`. Establish `hy : y ∈ Λ` using `(CoordTerm.mem_lat c Λ y).1 hx`. Establish `hyα : y = ∑ i, α i • t.f i`. Apply `c.e.injective` to reduce the goal to its premises.

Rewrite using `[hxα, map_sum]`. Simplify using `only [map_smul, hNf]`. Both sides reduce to the same expression. Establish `hyE : y ∈ Submodule.span E (Set.range (H.MMfam t))`. Rewrite using `[hyα]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfE.1 i)`. Use `(mem_span_of_Mof S hli (hMc y hy hyE)).1 ?_` and prove the remaining obligations. Rewrite using `[hxα]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce `hx`.

Use `⟨(Submodule.span_le.2 ?_) hx, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩ show c.grp n0 (S.f b) ∈ c.lat Λ`. Rewrite using `[hNf, CoordTerm.mem_lat]`. Conclude with `hfm b`. Establish `h1 : Submodule.span M.L.O (Set.range fun b => c.grp n0 (S.f b)) ≤ (S.spanTo S.f (r + 1)).restrictScalars M.L.O`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `TermBasic.map_mem hg hN (r + 1) (TermBasic.self_mem S S.f b.2)`. Conclude with `h1 hx`. Establish `htr' : ∀ x, (x ∈ c.lat Λ ∧ x ∈ S.spanTo S.f' (r + 1)) ↔ x ∈ Submodule.span M.L.O (Set.range fun b => c.grp n0' (S.f' b))`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hxs⟩`. Establish `hx' : (c.grp n0').symm x ∈ S.spanTo S.f' (r + 1)` using `(TermBasic.map_mem_iff hg' hN' (r + 1) _).1 (by simpa using hxs)`. Rewrite `hx'` using `[TermBasic.spanTo_top]`.

Take `⟨α, hα⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hx'`. Establish `hxα : x = ∑ i, α i • c.grp n0' (S.f' i)`. Use `congrArg (c.grp n0') hα` as an intermediate fact. Simplify `this.symm` using `[map_sum, map_smul]`. Take `⟨y, rfl⟩` from `c.e.surjective x`.

Establish `hy : y ∈ Λ` using `(CoordTerm.mem_lat c Λ y).1 hx`. Establish `hyα : y = ∑ i, α i • t.f' i`. Apply `c.e.injective` to reduce the goal to its premises. Rewrite using `[hxα, map_sum]`. Simplify using `only [map_smul, hNf']`.

Both sides reduce to the same expression. Establish `hyE : y ∈ Submodule.span E (Set.range (H.MMfam t))`. Rewrite using `[hyα]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `h1 : t.f' i = t.f i + algebraMap F E (LocNG.theta M) • (algebraMap F E (LocNG.theta M)⁻¹ • (t.f' i - t.f i))`.

Rewrite using `[smul_smul, ← map_mul, mul_inv_cancel₀ hθ, map_one, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[h1]`. Conclude with `Submodule.add_mem _ (hfE.1 i) (Submodule.smul_mem _ _ (hfE.2 i))`. Use `(mem_span_of_Mof S hli (hMc y hy hyE)).2 ?_` and prove the remaining obligations.

Rewrite using `[hxα]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce `hx`. Use `⟨(Submodule.span_le.2 ?_) hx, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩ show c.grp n0' (S.f' b) ∈ c.lat Λ`.

Rewrite using `[hNf', CoordTerm.mem_lat]`. Conclude with `hfm' b`. Establish `h1 : Submodule.span M.L.O (Set.range fun b => c.grp n0' (S.f' b)) ≤ (S.spanTo S.f' (r + 1)).restrictScalars M.L.O`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`.

Conclude with `TermBasic.map_mem hg' hN' (r + 1) (TermBasic.self_mem S S.f' b.2)`. Conclude with `h1 hx`. Take `⟨A, hA, n₁, hn₁, hn₁f, e1⟩` from `FrameLift.lift M.L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) (c.lat Λ) hsdc _ hN htr`. Take `⟨A', hA', n₁', hn₁', hn₁f', e1'⟩` from `FrameLift.lift M.L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) (c.lat Λ) hsdc _ hN' htr'`. Establish `hW : S.IsTermW (A, A', S.graphOf (c.lat Λ)) (c.lat Λ) n₁ n₁'`.

Use `⟨hA, hA', hn₁, hn₁', e1, e1', fun b => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hn₁f, hn₁f', hNf, hNf', ← map_sub, CoordTerm.inTh_iff, ← hth, CoordTerm.mem_smulLat]`. Use `⟨_, hdm b, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, ← map_mul, mul_inv_cancel₀ hθ, map_one, one_smul]`. Take `⟨d, hd⟩` from `(CoordTermWt.terms_correspond M hM H r k P S c).2.2 _ _ ⟨(n₁, n₁'), hW⟩`.

Establish `hW2 : S.IsTermW (c.dat d) (c.lat Λ) (c.grp (c.grp.symm n₁)) (c.grp (c.grp.symm n₁'))`. Rewrite using `[← hd, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]`. Conclude with `hW`. Take `⟨hto, -⟩` from `(CoordTerm.isTermW_iff M hM H r k P S c d _ _ Λ).2 hW2`. Establish `e3 : (fun b => (c.grp.symm n₁) (P.A.f b)) = fun b => n0 (P.A.f b)`.

Use function extensionality and compare the values at `fun b => c.e.injective (by`. Rewrite using `[← CoordTerm.grp_e, MulEquiv.apply_symm_apply, ← c.f_eq, hn₁f, hNf])`. Establish `e4 : (fun b => (c.grp.symm n₁') (P.B.f b)) = fun b => n0' (P.B.f b)`. Use function extensionality and compare the values at `fun b => c.e.injective (by`. Rewrite using `[← CoordTerm.grp_e, MulEquiv.apply_symm_apply, ← c.f'_eq, hn₁f', hNf'])`.

Rewrite `hto` using `[e3, e4]`. Conclude with `⟨d, hto, hbb⟩`.
-/
theorem generic_terms : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ Λ : Submodule M.L.O V, ((H.IsSelfDual Λ ∧ Λ.FG ∧ (∀ i, H.MMfam (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) i ∈ Λ) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ↔ ∃ d : LocNG.Datum P, LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ∧ ∀ d d' : LocNG.Datum P, LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) → LocNG.IsTermOver P d' (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) → d = d' := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP f f' hf hf' Λ
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := CoordExist.exists_coord M hM H r k P hrk hP
  obtain ⟨hth, hNA, hNB, -, -, -, -, -, -⟩ := CoordUnip.transport M hM H r k P S c
  have hTL := GlobalTheory.LocOver.TermLat.datum_of_lattice M hM H r k P hrk hP
  have hθ : LocNG.theta M ≠ 0 := by rw [hth]; exact CoordTermWt.th_ne S
  refine ⟨⟨fun hL => ?_, fun hR => ?_⟩, fun d d' hd hd' => ?_⟩
  rotate_left
  ·
    obtain ⟨d, hd, hbb⟩ := hR
    obtain ⟨hT, -, -⟩ := hTL.1 d _ hd
    obtain ⟨hsd, hfr, hfr', -, -, hadm⟩ := hT
    refine ⟨hsd, hsd.1, ?_, hbb⟩
    refine (CoordTermWt.fam_mem (H := H) _ Λ).2 ⟨hfr.1.1, fun b => ?_⟩
    rcases hs : M.split with _ | g
    · have h1 : LocNG.theta M = 1 := by simp [LocNG.theta, hs]
      rw [h1, inv_one, map_one, one_smul]
      exact Λ.sub_mem (hfr'.1.1 b) (hfr.1.1 b)
    · have h1 : LocNG.theta M = (g.q : F) := by simp [LocNG.theta, hs]
      obtain ⟨y, hy, e⟩ := (CoordTerm.mem_smulLat (H := H) _ Λ _).1 ((hadm g hs).2.2 b)
      show algebraMap F E (LocNG.theta M)⁻¹ • (f' b - f b) ∈ Λ
      rw [show f' b - f b = _ from e, smul_smul, ← map_mul, ← h1, inv_mul_cancel₀ hθ, map_one, one_smul]
      exact hy
  ·
    exact hTL.2 d d' _ _ hd hd' rfl rfl (fun _ _ => rfl)
  · obtain ⟨hsd, -, hmm, hbb⟩ := hL
    obtain ⟨n0, hn0, rfl⟩ := hf
    obtain ⟨n0', hn0', rfl⟩ := hf'

    have hg : ∀ a (j : Fin r), hf M.L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
      simp [S.gram, Fin.castSucc_ne_last]
    have hg' : ∀ a (j : Fin r), hf M.L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
      simp [S.gram', Fin.castSucc_ne_last]
    have hN : c.grp n0 ∈ S.N := (hNA n0).1 hn0
    have hN' : c.grp n0' ∈ S.N' := (hNB n0').1 hn0'
    have hNf : ∀ b, c.grp n0 (S.f b) = c.e (n0 (P.A.f b)) := fun b => by rw [c.f_eq, CoordTerm.grp_e]
    have hNf' : ∀ b, c.grp n0' (S.f' b) = c.e (n0' (P.B.f b)) := fun b => by
      rw [c.f'_eq, CoordTerm.grp_e]
    set t : Term V M r := ⟨Λ, fun b => n0 (P.A.f b), fun b => n0' (P.B.f b), P.A.T, P.B.T⟩ with ht
    obtain ⟨hfm, hdm⟩ := (CoordTermWt.fam_mem (H := H) t Λ).1 hmm
    have hfm' : ∀ b, n0' (P.B.f b) ∈ Λ := fun b => by
      have h1 : n0' (P.B.f b) = n0 (P.A.f b) +
          algebraMap F E (LocNG.theta M) • (algebraMap F E (LocNG.theta M)⁻¹ • (t.f' b - t.f b)) := by
        rw [smul_smul, ← map_mul, mul_inv_cancel₀ hθ, map_one, one_smul]
        simp [ht]
      rw [h1]
      exact Λ.add_mem (hfm b) (Λ.smul_mem (⟨_, theta_mem M⟩ : M.L.O) (hdm b))
    have hli := MoveSame.indep S hN hN'
    have hsdc := isSD_lat c Λ hsd

    have hMc : ∀ y ∈ Λ, y ∈ Submodule.span E (Set.range (H.MMfam t)) →
        c.e y ∈ S.Mof (fun b => c.grp n0 (S.f b)) (fun b => c.grp n0' (S.f' b)) := by
      intro y hy hyE
      have hyO : y ∈ Submodule.span M.L.O (Set.range (H.MMfam t)) := by
        by_contra h
        exact hbb ⟨y, hy, hyE, h⟩
      have e1 : (fun b => c.grp n0 (S.f b)) = fun b => c.e (t.f b) := funext hNf
      have e2 : (fun b => c.grp n0' (S.f' b)) = fun b => c.e (t.f' b) := funext hNf'
      rw [e1, e2, ← CoordTermWt.lat_span c t]
      exact (CoordTerm.mem_lat c _ y).2 hyO
    have hfE := ((CoordTermWt.fam_mem (H := H) t (Submodule.span E (Set.range (H.MMfam t)))).1
      (fun i => Submodule.subset_span ⟨i, rfl⟩))
    have htr : ∀ x, (x ∈ c.lat Λ ∧ x ∈ S.spanTo S.f (r + 1)) ↔
        x ∈ Submodule.span M.L.O (Set.range fun b => c.grp n0 (S.f b)) := by
      intro x
      constructor
      · rintro ⟨hx, hxs⟩
        have hx' : (c.grp n0).symm x ∈ S.spanTo S.f (r + 1) :=
          (TermBasic.map_mem_iff hg hN (r + 1) _).1 (by simpa using hxs)
        rw [TermBasic.spanTo_top] at hx'
        obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx'
        have hxα : x = ∑ i, α i • c.grp n0 (S.f i) := by
          have := congrArg (c.grp n0) hα
          simpa [map_sum, map_smul] using this.symm
        obtain ⟨y, rfl⟩ := c.e.surjective x
        have hy : y ∈ Λ := (CoordTerm.mem_lat c Λ y).1 hx
        have hyα : y = ∑ i, α i • t.f i := by
          apply c.e.injective
          rw [hxα, map_sum]
          simp only [map_smul, hNf]
          rfl
        have hyE : y ∈ Submodule.span E (Set.range (H.MMfam t)) := by
          rw [hyα]
          exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfE.1 i)
        refine (mem_span_of_Mof S hli (hMc y hy hyE)).1 ?_
        rw [hxα]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · intro hx
        refine ⟨(Submodule.span_le.2 ?_) hx, ?_⟩
        · rintro _ ⟨b, rfl⟩
          show c.grp n0 (S.f b) ∈ c.lat Λ
          rw [hNf, CoordTerm.mem_lat]
          exact hfm b
        · have h1 : Submodule.span M.L.O (Set.range fun b => c.grp n0 (S.f b)) ≤
              (S.spanTo S.f (r + 1)).restrictScalars M.L.O := by
            refine Submodule.span_le.2 ?_
            rintro _ ⟨b, rfl⟩
            exact TermBasic.map_mem hg hN (r + 1) (TermBasic.self_mem S S.f b.2)
          exact h1 hx
    have htr' : ∀ x, (x ∈ c.lat Λ ∧ x ∈ S.spanTo S.f' (r + 1)) ↔
        x ∈ Submodule.span M.L.O (Set.range fun b => c.grp n0' (S.f' b)) := by
      intro x
      constructor
      · rintro ⟨hx, hxs⟩
        have hx' : (c.grp n0').symm x ∈ S.spanTo S.f' (r + 1) :=
          (TermBasic.map_mem_iff hg' hN' (r + 1) _).1 (by simpa using hxs)
        rw [TermBasic.spanTo_top] at hx'
        obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx'
        have hxα : x = ∑ i, α i • c.grp n0' (S.f' i) := by
          have := congrArg (c.grp n0') hα
          simpa [map_sum, map_smul] using this.symm
        obtain ⟨y, rfl⟩ := c.e.surjective x
        have hy : y ∈ Λ := (CoordTerm.mem_lat c Λ y).1 hx
        have hyα : y = ∑ i, α i • t.f' i := by
          apply c.e.injective
          rw [hxα, map_sum]
          simp only [map_smul, hNf']
          rfl
        have hyE : y ∈ Submodule.span E (Set.range (H.MMfam t)) := by
          rw [hyα]
          refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
          have h1 : t.f' i = t.f i +
              algebraMap F E (LocNG.theta M) • (algebraMap F E (LocNG.theta M)⁻¹ • (t.f' i - t.f i)) := by
            rw [smul_smul, ← map_mul, mul_inv_cancel₀ hθ, map_one, one_smul]
            abel
          rw [h1]
          exact Submodule.add_mem _ (hfE.1 i) (Submodule.smul_mem _ _ (hfE.2 i))
        refine (mem_span_of_Mof S hli (hMc y hy hyE)).2 ?_
        rw [hxα]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · intro hx
        refine ⟨(Submodule.span_le.2 ?_) hx, ?_⟩
        · rintro _ ⟨b, rfl⟩
          show c.grp n0' (S.f' b) ∈ c.lat Λ
          rw [hNf', CoordTerm.mem_lat]
          exact hfm' b
        · have h1 : Submodule.span M.L.O (Set.range fun b => c.grp n0' (S.f' b)) ≤
              (S.spanTo S.f' (r + 1)).restrictScalars M.L.O := by
            refine Submodule.span_le.2 ?_
            rintro _ ⟨b, rfl⟩
            exact TermBasic.map_mem hg' hN' (r + 1) (TermBasic.self_mem S S.f' b.2)
          exact h1 hx

    obtain ⟨A, hA, n₁, hn₁, hn₁f, e1⟩ :=
      FrameLift.lift M.L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) (c.lat Λ) hsdc _ hN htr
    obtain ⟨A', hA', n₁', hn₁', hn₁f', e1'⟩ :=
      FrameLift.lift M.L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) (c.lat Λ) hsdc _ hN' htr'
    have hW : S.IsTermW (A, A', S.graphOf (c.lat Λ)) (c.lat Λ) n₁ n₁' := by
      refine ⟨hA, hA', hn₁, hn₁', e1, e1', fun b => ?_, rfl⟩
      rw [hn₁f, hn₁f', hNf, hNf', ← map_sub, CoordTerm.inTh_iff, ← hth, CoordTerm.mem_smulLat]
      refine ⟨_, hdm b, ?_⟩
      rw [smul_smul, ← map_mul, mul_inv_cancel₀ hθ, map_one, one_smul]
    obtain ⟨d, hd⟩ := (CoordTermWt.terms_correspond M hM H r k P S c).2.2 _ _ ⟨(n₁, n₁'), hW⟩
    have hW2 : S.IsTermW (c.dat d) (c.lat Λ) (c.grp (c.grp.symm n₁)) (c.grp (c.grp.symm n₁')) := by
      rw [← hd, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact hW
    obtain ⟨hto, -⟩ := (CoordTerm.isTermW_iff M hM H r k P S c d _ _ Λ).2 hW2
    have e3 : (fun b => (c.grp.symm n₁) (P.A.f b)) = fun b => n0 (P.A.f b) :=
      funext fun b => c.e.injective (by
        rw [← CoordTerm.grp_e, MulEquiv.apply_symm_apply, ← c.f_eq, hn₁f, hNf])
    have e4 : (fun b => (c.grp.symm n₁') (P.B.f b)) = fun b => n0' (P.B.f b) :=
      funext fun b => c.e.injective (by
        rw [← CoordTerm.grp_e, MulEquiv.apply_symm_apply, ← c.f'_eq, hn₁f', hNf'])
    rw [e3, e4] at hto
    exact ⟨d, hto, hbb⟩

end GlobalTheory.HL.GenericTerm
