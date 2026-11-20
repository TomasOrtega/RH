import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupOfEventuallyPolynomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimConeImageOfBirationalLinearSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPieceFinrankLeH0Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLineBundleSectionsLeImageFormsStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

open AlgebraicGeometry Filter GlobalTheory.CompHt
open scoped ENNReal

set_option autoImplicit false

namespace GlobalTheory.ImageDegree

/- English proof (translation)
Establish `hf : (0 : ℝ) < D.factorial` using `by positivity`. Establish `h2 : Tendsto (fun m : ℕ => ENNReal.ofReal ((D.factorial : ℝ) * ((r m : ℝ) / (m : ℝ) ^ D))) atTop (nhds (ENNReal.ofReal c))`. Use `ENNReal.tendsto_ofReal ?_` and prove the remaining obligations. Use `h.const_mul (D.factorial : ℝ)` as an intermediate fact. Rewrite `this` using `[mul_div_cancel₀ _ hf.ne']`. Then use the resulting hypothesis.

Use `(Tendsto.limsup_eq ?_)` and prove the remaining obligations. Use `h2.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop 0] with m hm`. Establish `hm' : (m : ℝ≥0∞) ^ D ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hm.ne')`. Establish `hm'' : (m : ℝ≥0∞) ^ D ≠ ⊤` using `ENNReal.pow_ne_top (ENNReal.natCast_ne_top m)`.

Rewrite using `[ENat.toENNReal_coe, mul_div_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]`.
-/
theorem growth_eq_of_tendsto (D : ℕ) (r : ℕ → ℕ) {c : ℝ} (hc : 0 ≤ c)
    (h : Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (nhds (c / D.factorial))) :
    growth D (fun m => (r m : ℕ∞)) = ENNReal.ofReal c := by
  have hf : (0 : ℝ) < D.factorial := by positivity
  have h2 : Tendsto (fun m : ℕ => ENNReal.ofReal ((D.factorial : ℝ) * ((r m : ℝ) / (m : ℝ) ^ D))) atTop
      (nhds (ENNReal.ofReal c)) := by
    refine ENNReal.tendsto_ofReal ?_
    have := h.const_mul (D.factorial : ℝ)
    rwa [mul_div_cancel₀ _ hf.ne'] at this
  refine (Tendsto.limsup_eq ?_)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm.ne')
  have hm'' : (m : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top m)
  rw [ENat.toENNReal_coe, mul_div_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast]

/- English proof (translation)
The claim follows from `GlobalTheory.T.ringKrullDim_cone_image_of_birational_linearSystem k S h hb hB`.
-/
theorem ringKrullDim_of_birational {k : Type} [Field k] (S : LinSys k) (h : S.IsVariety) (hb : S.BasePointFree)
    (hB : S.Birational) : ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = (S.D + 1 : ℕ) :=
  GlobalTheory.T.ringKrullDim_cone_image_of_birational_linearSystem k S h hb hB

/- English proof (translation)
The claim follows from `GlobalTheory.T.quotient_piece_finrank_le_h0 k S h m`.
-/
theorem finrank_quotientPiece_le_lineBundleSections {k : Type} [Field k] (S : LinSys k) (h : S.IsVariety) (m : ℕ) :
    Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) ≤ lbH0 k (lbPow S.L m) :=
  GlobalTheory.T.quotient_piece_finrank_le_h0 k S h m

/- English proof (translation)
The claim follows from `GlobalTheory.T.rankGrowth_lineBundle_sections_le_image_forms k S h hb hB`.
-/
theorem rankGrowth_lineBundleSections_le_image_forms {k : Type} [Field k] [CharZero k] (S : LinSys k) (h : S.IsVariety) (hb : S.BasePointFree)
    (hB : S.Birational) :
    growth S.D (fun m => (lbH0 k (lbPow S.L m) : ℕ∞)) ≤
      growth S.D (fun m => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) :=
  GlobalTheory.T.rankGrowth_lineBundle_sections_le_image_forms k S h hb hB

/- English proof (translation)
Use `HeightExists.isIntegral h` as an intermediate fact. Establish `hc (U : S.Y.Opens) (hU : IsAffineOpen U) (hne : (U : Set S.Y).Nonempty) : topologicalKrullDim (U : Set S.Y) = S.D`. Rewrite using `[topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]`. Conclude with `(PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(S.Y, U))).trans (SmoothDim.ringKrullDim_affineOpen k _ S.str _ h.smooth U hU hne)`. Use `le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_` and prove the remaining obligations.

Take `⟨U, hU, hx, -⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.Y.isBasis_affineOpens (TopologicalSpace.Opens.mem_top x)`. Conclude with `⟨U, U.isOpen, hx, (hc U hU ⟨x, hx⟩).le⟩`. Take `⟨U, hU, hx, -⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.Y.isBasis_affineOpens (TopologicalSpace.Opens.mem_top (genericPoint S.Y))`. Conclude with `(hc U hU ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)`.
-/
theorem topologicalKrullDim_eq {k : Type} [Field k] (S : LinSys k) (h : S.IsVariety) :
    topologicalKrullDim S.Y = S.D := by
  have := HeightExists.isIntegral h
  have hc (U : S.Y.Opens) (hU : IsAffineOpen U) (hne : (U : Set S.Y).Nonempty) :
      topologicalKrullDim (U : Set S.Y) = S.D := by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(S.Y, U))).trans
      (SmoothDim.ringKrullDim_affineOpen k _ S.str _ h.smooth U hU hne)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top x)
    exact ⟨U, U.isOpen, hx, (hc U hU ⟨x, hx⟩).le⟩
  · obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (genericPoint S.Y))
    exact (hc U hU ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

/- English proof (translation)
Introduce `Q F _ _ S hV hb hB`. Establish `hdim` using `ringKrullDim_of_birational S hV hb hB`. Establish `hp` using `HeightExists.isPrime_imageIdeal hV`. Establish `hI` using `S.isHomogeneous_imageIdeal`. Establish `hdeg` using `degree_idealHilbertPoly_eq_of_isPrime hI hdim`.

Establish `hHG` using `(growth_of_eventually_eq_eval S.D 1 (fun m => Module.finrank F (quotPiece S.imageIdeal (m : ℤ))) (idealHilbertPoly S.imageIdeal) le_rfl (eventually_finrank_quotPiece hI)).1 hdeg.le (hilbertDegree S.imageIdeal) (cast_hilbertDegree_of_degree_eq hI hdeg)`. Simplify using `only [one_mul, Nat.cast_one, one_pow] at hHG`. Establish `hHG' : growth S.D (fun m => (Module.finrank F (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) = hilbertDegree S.imageIdeal`. Use `Eq.trans ?_ hHG` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `m`. Rewrite using `[one_mul]`. Establish `hstr : strHom F S.Y = S.str` using `strHom_eq fun _ => rfl`. Establish `hproj : IsProjOver (strHom F S.Y)` using `hstr ▸ hV.proj`. Establish `hnef : IsNef F S.L` using `IsGenerated.isNef_of_isProjOver ⟨S.N, S.b, hb⟩ hV.proj`.

Establish `hYd` using `topologicalKrullDim_eq S hV`. Establish `h0` using `Q.nef.2.2.topSelf_nonneg hproj hYd hnef`. Establish `hG` using `growth_eq_of_tendsto S.D (fun m => lbH0 F (lbPow S.L m)) (Int.cast_nonneg h0) (Q.nef.2.2.tendsto hproj hYd hnef)`. Establish `hle1 : growth S.D (fun m => (Module.finrank F (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) ≤ growth S.D (fun m => (lbH0 F (lbPow S.L m) : ℕ∞))` using `limsup_le_limsup (Eventually.of_forall fun m => ENNReal.div_le_div_right (mul_le_mul_right (ENat.toENNReal_le.2 (Nat.cast_le.2 (finrank_quotientPiece_le_lineBundleSections S hV m))) _) _)`. Establish `hle2` using `rankGrowth_lineBundleSections_le_image_forms S hV hb hB`.

Rewrite `hle1`, `hle2` using `[hHG', hG]`. Establish `e : (hilbertDegree S.imageIdeal : ℝ≥0∞) = ENNReal.ofReal (topSelfIntersection F S.L S.D : ℝ)` using `le_antisymm hle1 hle2`. Establish `e' : ((hilbertDegree S.imageIdeal : ℝ) : ℝ) = (topSelfIntersection F S.L S.D : ℝ)`. Rewrite `e` using `[← ENNReal.ofReal_natCast]`. Conclude with `(ENNReal.ofReal_eq_ofReal_iff (by positivity) (Int.cast_nonneg h0)).1 e`.

Establish `hdel : (hilbertDegree S.imageIdeal : ℤ) = S.del`. Rewrite using `[LinSys.del]`. Conclude with `e'` after adjusting the coercions. Take `⟨Ω, _, _, x, hx, -⟩` from `HeightExists.exists_generic hV`. Take `⟨j, hj⟩` from `Function.ne_iff.1 (hb.coords_ne_zero x.1)`.

Establish `hX : (X j : MvPolynomial (Fin S.N) F) ∉ S.imageIdeal` using `fun hX => hj (by simpa using S.eval₂_coords_eq_zero x.1 hX)`. Establish `hpos` using `hilbertDegree_pos hI hX`. Conclude with `⟨hdel ▸ (by exact_mod_cast hpos), hdel, hdim⟩`.
-/
theorem degree_image_eq_topSelf : Quoted → ∀ (F : Type) [Field F] [NumberField F] (S : LinSys F), S.IsVariety → S.BasePointFree →
    S.Birational → 0 < S.del ∧ (hilbertDegree S.imageIdeal : ℤ) = S.del ∧
      ringKrullDim (MvPolynomial (Fin S.N) F ⧸ S.imageIdeal) = (S.D + 1 : ℕ) := by
  intro Q F _ _ S hV hb hB
  have hdim := ringKrullDim_of_birational S hV hb hB
  have hp := HeightExists.isPrime_imageIdeal hV
  have hI := S.isHomogeneous_imageIdeal
  have hdeg := degree_idealHilbertPoly_eq_of_isPrime hI hdim
  have hHG := (growth_of_eventually_eq_eval S.D 1 (fun m => Module.finrank F (quotPiece S.imageIdeal (m : ℤ)))
    (idealHilbertPoly S.imageIdeal) le_rfl (eventually_finrank_quotPiece hI)).1 hdeg.le (hilbertDegree S.imageIdeal)
    (cast_hilbertDegree_of_degree_eq hI hdeg)
  simp only [one_mul, Nat.cast_one, one_pow] at hHG
  have hHG' : growth S.D (fun m => (Module.finrank F (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) = hilbertDegree S.imageIdeal := by
    refine Eq.trans ?_ hHG
    congr 1
    funext m
    rw [one_mul]
  have hstr : strHom F S.Y = S.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom F S.Y) := hstr ▸ hV.proj
  have hnef : IsNef F S.L := IsGenerated.isNef_of_isProjOver ⟨S.N, S.b, hb⟩ hV.proj
  have hYd := topologicalKrullDim_eq S hV
  have h0 := Q.nef.2.2.topSelf_nonneg hproj hYd hnef
  have hG := growth_eq_of_tendsto S.D (fun m => lbH0 F (lbPow S.L m)) (Int.cast_nonneg h0)
    (Q.nef.2.2.tendsto hproj hYd hnef)
  have hle1 : growth S.D (fun m => (Module.finrank F (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) ≤
      growth S.D (fun m => (lbH0 F (lbPow S.L m) : ℕ∞)) :=
    limsup_le_limsup (Eventually.of_forall fun m => ENNReal.div_le_div_right (mul_le_mul_right
      (ENat.toENNReal_le.2 (Nat.cast_le.2 (finrank_quotientPiece_le_lineBundleSections S hV m))) _) _)
  have hle2 := rankGrowth_lineBundleSections_le_image_forms S hV hb hB
  rw [hHG', hG] at hle1 hle2
  have e : (hilbertDegree S.imageIdeal : ℝ≥0∞) = ENNReal.ofReal (topSelfIntersection F S.L S.D : ℝ) := le_antisymm hle1 hle2
  have e' : ((hilbertDegree S.imageIdeal : ℝ) : ℝ) = (topSelfIntersection F S.L S.D : ℝ) := by
    rw [← ENNReal.ofReal_natCast] at e
    exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (Int.cast_nonneg h0)).1 e
  have hdel : (hilbertDegree S.imageIdeal : ℤ) = S.del := by
    rw [LinSys.del]; exact_mod_cast e'
  obtain ⟨Ω, _, _, x, hx, -⟩ := HeightExists.exists_generic hV
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero x.1)
  have hX : (X j : MvPolynomial (Fin S.N) F) ∉ S.imageIdeal := fun hX => hj (by simpa using S.eval₂_coords_eq_zero x.1 hX)
  have hpos := hilbertDegree_pos hI hX
  exact ⟨hdel ▸ (by exact_mod_cast hpos), hdel, hdim⟩

end GlobalTheory.ImageDegree
