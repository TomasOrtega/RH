import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.StabFix

section Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

/- English proof (translation)
Take `⟨_, hcompl, -⟩` from `GlobalTheory.FrameBasic.main L r k S`. Establish `hW0` using `(GlobalTheory.HL.FrameStab.stab_eq L r k S).1 h hS`. Establish `hHe : IsHerm L S.Hm` using `S.herm.1`. Establish `hN : h ∈ S.N` using `(Subgroup.mem_inf.1 hS).1`. Simplify using `only [Frames.N, Frames.Nof, Subgroup.mem_inf] at hN`.

Take `⟨⟨hiso, -⟩, hU⟩` from `hN`. Establish `hiso' : ∀ x y, hf L S.Hm (h x) (h y) = hf L S.Hm x y` using `hiso`. Take `⟨-, hU2⟩` from `hU`. Establish `hfX : ∀ a, S.f a ∈ perp L S.Hm (S.spanTo S.f r)`. Introduce `a`.

Rewrite using `[Frames.spanTo, Set.image_eq_range, GlobalTheory.FrameBasic.mem_perp_span L hHe]`. Introduce and unpack `⟨j, hj⟩`. Rewrite using `[S.gram]`. Establish `: j ≠ Fin.last r`. Introduce `e`.

Simplify using `[e] at hj`. Simplify using `[this]`. Establish `hXle : S.spanTo S.f r ≤ S.ME`. Use `le_trans (Submodule.span_mono (Set.image_mono ?_)) le_sup_left` and prove the remaining obligations. Introduce `i hi`.

Conclude with `Nat.lt_succ_of_lt hi`. Establish `hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f'))`. Rewrite using `[Frames.ME, GlobalTheory.HL.FrameStab.spanTo_top, GlobalTheory.HL.FrameStab.spanTo_top, Set.Sum.elim_range, Submodule.span_union]`. Establish `hsub : ∀ a b y, hf L S.Hm (a - b) y = hf L S.Hm a y - hf L S.Hm b y` using `fun a b y => (GlobalTheory.FrameBasic.hfL L S.Hm y).map_sub a b`. Establish `hfix : ∀ a, h (S.f a) = S.f a`.

Introduce `a`. Establish `hu : h (S.f a) - S.f a ∈ S.spanTo S.f r` using `hU2 _ (hfX a)`. Establish `hW : h (S.f a) - S.f a ∈ S.W0`. Rewrite using `[Frames.W0, hME, GlobalTheory.FrameBasic.mem_perp_span L hHe]`. Introduce and unpack `(i | b)`.

Simplify using `only [Sum.elim_inl]`. Rewrite using `[GlobalTheory.FrameBasic.hf_conj L hHe, hfX i _ hu, map_zero]`. Simplify using `only [Sum.elim_inr]`. Rewrite using `[hsub, ← hf' b, hiso', hf' b, sub_self]`. Use `(Submodule.disjoint_def.1 hcompl.disjoint) _ (hXle hu) hW` as an intermediate fact.

Conclude with `sub_eq_zero.1 this`. Establish `hall : ∀ v, h v = v`. Introduce `v`. Establish `hv : v ∈ S.ME ⊔ S.W0` using `by rw [hcompl.sup_eq_top]; trivial`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hv`.

Establish `hy' : y ∈ LinearMap.eqLocus (h : S.V →ₗ[E] S.V) LinearMap.id`. Establish `: S.ME ≤ LinearMap.eqLocus (h : S.V →ₗ[E] S.V) LinearMap.id`. Rewrite using `[hME, Submodule.span_le]`. Introduce and unpack `_ ⟨i | b, rfl⟩`. Conclude with `hfix i`.

Conclude with `hf' b`. Conclude with `this hy`. Rewrite using `[map_add, hW0 z hz]`. Rewrite `hy'` using `[LinearMap.mem_eqLocus]`. Rewrite using `[show h y = y from hy']`.

Conclude with `LinearEquiv.ext hall`.
-/
theorem local_eq_one (h : S.GLV) (hS : h ∈ S.St) (hf' : ∀ b, h (S.f' b) = S.f' b) : h = 1 := by
  obtain ⟨_, hcompl, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hW0 := (GlobalTheory.HL.FrameStab.stab_eq L r k S).1 h hS
  have hHe : IsHerm L S.Hm := S.herm.1
  have hN : h ∈ S.N := (Subgroup.mem_inf.1 hS).1
  simp only [Frames.N, Frames.Nof, Subgroup.mem_inf] at hN
  obtain ⟨⟨hiso, -⟩, hU⟩ := hN
  have hiso' : ∀ x y, hf L S.Hm (h x) (h y) = hf L S.Hm x y := hiso
  obtain ⟨-, hU2⟩ := hU

  have hfX : ∀ a, S.f a ∈ perp L S.Hm (S.spanTo S.f r) := by
    intro a
    rw [Frames.spanTo, Set.image_eq_range, GlobalTheory.FrameBasic.mem_perp_span L hHe]
    rintro ⟨j, hj⟩
    rw [S.gram]
    have : j ≠ Fin.last r := by
      intro e; simp [e] at hj
    simp [this]
  have hXle : S.spanTo S.f r ≤ S.ME := by
    refine le_trans (Submodule.span_mono (Set.image_mono ?_)) le_sup_left
    intro i hi
    exact Nat.lt_succ_of_lt hi
  have hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f')) := by
    rw [Frames.ME, GlobalTheory.HL.FrameStab.spanTo_top, GlobalTheory.HL.FrameStab.spanTo_top, Set.Sum.elim_range,
      Submodule.span_union]
  have hsub : ∀ a b y, hf L S.Hm (a - b) y = hf L S.Hm a y - hf L S.Hm b y := fun a b y =>
    (GlobalTheory.FrameBasic.hfL L S.Hm y).map_sub a b
  have hfix : ∀ a, h (S.f a) = S.f a := by
    intro a
    have hu : h (S.f a) - S.f a ∈ S.spanTo S.f r := hU2 _ (hfX a)
    have hW : h (S.f a) - S.f a ∈ S.W0 := by
      rw [Frames.W0, hME, GlobalTheory.FrameBasic.mem_perp_span L hHe]
      rintro (i | b)
      · simp only [Sum.elim_inl]
        rw [GlobalTheory.FrameBasic.hf_conj L hHe, hfX i _ hu, map_zero]
      · simp only [Sum.elim_inr]
        rw [hsub, ← hf' b, hiso', hf' b, sub_self]
    have := (Submodule.disjoint_def.1 hcompl.disjoint) _ (hXle hu) hW
    exact sub_eq_zero.1 this
  have hall : ∀ v, h v = v := by
    intro v
    have hv : v ∈ S.ME ⊔ S.W0 := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    have hy' : y ∈ LinearMap.eqLocus (h : S.V →ₗ[E] S.V) LinearMap.id := by
      have : S.ME ≤ LinearMap.eqLocus (h : S.V →ₗ[E] S.V) LinearMap.id := by
        rw [hME, Submodule.span_le]
        rintro _ ⟨i | b, rfl⟩
        · exact hfix i
        · exact hf' b
      exact this hy
    rw [map_add, hW0 z hz]
    rw [LinearMap.mem_eqLocus] at hy'
    rw [show h y = y from hy']
  exact LinearEquiv.ext hall
end Loc

/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 F)`. Conclude with `⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩`.
-/
theorem nonempty_place (F : Type) [Field F] [NumberField F] : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig A r k G x hx hfix`. Take `⟨p⟩` from `nonempty_place F`. Use `(A.loc p).lf` as an intermediate fact. Use `(A.loc p).char0` as an intermediate fact. Take `⟨x', hx'St, hext⟩` from `hx p`.

Establish `hloc : ∀ b, x' ((G.S p).f' b) = (G.S p).f' b`. Introduce `b`. Set `u : ((A.loc p).Ep)ˣ` to `Units.map (algebraMap (A.loc p).Fp (A.loc p).Ep).toMonoidHom (G.c p ^ (r - (b : ℕ)))`. Establish `hu : ((u : (A.loc p).Ep)) = algebraMap (A.loc p).Fp (A.loc p).Ep ((G.c p : (A.loc p).Fp) ^ (r - (b : ℕ)))`. Simplify using `[u]`.

Establish `h1 : x' ((u : (A.loc p).Ep) • (G.S p).f' b) = (u : (A.loc p).Ep) • (G.S p).f' b`. Rewrite using `[hu, G.f'_eq p b, hext, hfix b]`. Rewrite `h1` using `[map_smul]`. Establish `h2` using `congrArg (fun v => ((u⁻¹ : ((A.loc p).Ep)ˣ) : (A.loc p).Ep) • v) h1`. Simplify `h2` using `[smul_smul]`.

Establish `h1 : x' = 1` using `local_eq_one (G.S p) x' hx'St hloc`. Establish `hinj` using `(GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).1`. Use `LinearEquiv.ext fun v => hinj ?_` and prove the remaining obligations. Rewrite using `[← hext v, h1]`. Both sides reduce to the same expression.
-/
theorem eq_one_of_fix : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St,
    (∀ b, x (G.f' b) = G.f' b) → x = 1 := by
  intro F E _ _ _ _ _ sig A r k G x hx hfix
  obtain ⟨p⟩ := nonempty_place F
  have := (A.loc p).lf
  have := (A.loc p).char0
  obtain ⟨x', hx'St, hext⟩ := hx p
  have hloc : ∀ b, x' ((G.S p).f' b) = (G.S p).f' b := by
    intro b
    let u : ((A.loc p).Ep)ˣ := Units.map (algebraMap (A.loc p).Fp (A.loc p).Ep).toMonoidHom (G.c p ^ (r - (b : ℕ)))
    have hu : ((u : (A.loc p).Ep)) = algebraMap (A.loc p).Fp (A.loc p).Ep ((G.c p : (A.loc p).Fp) ^ (r - (b : ℕ))) := by
      simp [u]
    have h1 : x' ((u : (A.loc p).Ep) • (G.S p).f' b) = (u : (A.loc p).Ep) • (G.S p).f' b := by
      rw [hu, G.f'_eq p b, hext, hfix b]
    rw [map_smul] at h1
    have h2 := congrArg (fun v => ((u⁻¹ : ((A.loc p).Ep)ˣ) : (A.loc p).Ep) • v) h1
    simpa [smul_smul] using h2
  have h1 : x' = 1 := local_eq_one (G.S p) x' hx'St hloc
  have hinj := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).1
  refine LinearEquiv.ext fun v => hinj ?_
  rw [← hext v, h1]
  rfl

end GlobalTheory.HL.StabFix
