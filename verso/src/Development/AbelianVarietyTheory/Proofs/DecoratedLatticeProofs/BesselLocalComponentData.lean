import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAMulMemIntAt
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos

namespace GlobalTheory.LineOffT

/- English proof (translation)
Establish `hne : Ideal.span {(T : 𝓞 E)} ≠ ⊤` using `fun h => by`. Establish `h1` using `congrArg Ideal.absNorm h`. Rewrite `h1` using `[Ideal.absNorm_span_natCast, Ideal.absNorm_top]`. Break down `(Nat.pow_eq_one.1 h1) with h2 | h2` into its components or cases. Conclude with `hT.one_lt.ne' h2`.

Conclude with `(Module.finrank_pos (R := ℤ) (M := 𝓞 E)).ne' h2`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hmem : (T : 𝓞 E) ∈ M` using `hle (Ideal.mem_span_singleton_self _)`. Conclude with `⟨⟨M, hM.isPrime, fun h => Nat.cast_ne_zero.2 hT.ne_zero (by rwa [h, Ideal.mem_bot] at hmem)⟩, hmem⟩`.
-/
theorem exists_place (E : Type) [Field E] [NumberField E] {T : ℕ} (hT : T.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 E), (T : 𝓞 E) ∈ P.asIdeal := by
  have hne : Ideal.span {(T : 𝓞 E)} ≠ ⊤ := fun h => by
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at h1
    rcases (Nat.pow_eq_one.1 h1) with h2 | h2
    · exact hT.one_lt.ne' h2
    · exact (Module.finrank_pos (R := ℤ) (M := 𝓞 E)).ne' h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : (T : 𝓞 E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨M, hM.isPrime, fun h => Nat.cast_ne_zero.2 hT.ne_zero (by rwa [h, Ideal.mem_bot] at hmem)⟩, hmem⟩

variable {D : D7}

/- English proof (translation)
Establish `h0 : (N : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 fun h => hN (by rw [h, Nat.cast_zero]; exact zero_mem _)`. Use `IsU.of_pres (inU _ h0).mul_inv ?_ ?_` and prove the remaining obligations. Use `UnitAt.incA_mul_mem_intAt (N := 1) (by rw [Int.cast_one]; exact (Ideal.ne_top_iff_one _).1 x.isPrime.ne_top) ?_` and prove the remaining obligations. Rewrite using `[one_smul]`. Conclude with `isIntegral_natCast _`.

Use `UnitAt.incA_mul_mem_intAt (c := (N : D.host.E)⁻¹) (N := (N : ℤ)) (by rwa [Int.cast_natCast]) ?_` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul, Int.cast_natCast, mul_inv_cancel₀ h0]`. Conclude with `isIntegral_one`.
-/
theorem isU_nat {x : GlobalTheory.FinPl.Pl D} {N : ℕ} (hN : (N : 𝓞 D.host.F) ∉ x.asIdeal) : IsU x (incA D (N : D.host.E)) := by
  have h0 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 fun h => hN (by rw [h, Nat.cast_zero]; exact zero_mem _)
  refine IsU.of_pres (inU _ h0).mul_inv ?_ ?_
  · refine UnitAt.incA_mul_mem_intAt (N := 1)
      (by rw [Int.cast_one]; exact (Ideal.ne_top_iff_one _).1 x.isPrime.ne_top) ?_
    rw [one_smul]
    exact isIntegral_natCast _
  · refine UnitAt.incA_mul_mem_intAt (c := (N : D.host.E)⁻¹) (N := (N : ℤ)) (by rwa [Int.cast_natCast]) ?_
    rw [zsmul_eq_mul, Int.cast_natCast, mul_inv_cancel₀ h0]
    exact isIntegral_one

/- English proof (translation)
Establish `hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E)` using `D.host.sqrtMinusD_sq`. Establish `hint : IsIntegral ℤ D.host.sqrtMinusD`. Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations. Rewrite using `[hsq]`. Conclude with `(isIntegral_natCast _).neg`.

Establish `hdp : D.host.d.Prime` using `D.host.hyp.2.1`. Establish `hd0 : (D.host.d : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hdp.ne_zero`. Establish `h0 : D.host.sqrtMinusD ≠ 0` using `fun e => by`. Rewrite `hsq` using `[e]`. Conclude with `hd0 (by simpa using hsq.symm)`.

Establish `hc0 : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `hdT : Nat.Coprime D.host.d T` using `(Nat.coprime_primes hdp hT).2 hd.symm`. Use `IsU.of_pres (xiU D).mul_inv ?_ ?_` and prove the remaining obligations. Use `UnitAt.incA_mul_mem_intAt (c := D.host.xi0) (N := ((Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℤ)) (by rw [Int.cast_natCast]; exact UnitAt.notMem_of_coprime hv (Nat.Coprime.mul_left hc hdT)) ?_` and prove the remaining obligations. Use `hint using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul, Host.xi0]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-hsq`. Use `UnitAt.incA_mul_mem_intAt (c := D.host.xi0⁻¹) (N := 1) (by rw [Int.cast_one]; exact (Ideal.ne_top_iff_one _).1 x.isPrime.ne_top) ?_` and prove the remaining obligations. Rewrite using `[one_smul, Host.xi0, inv_div, div_neg, div_one]`.

Conclude with `((isIntegral_natCast _).mul hint).neg`.
-/
theorem isU_xi_of_prime {x : GlobalTheory.FinPl.Pl D} {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 D.host.F) ∈ x.asIdeal)
    (hd : T ≠ D.host.d) (hc : Nat.Coprime (Ideal.absNorm D.host.ccK) T) : IsU x (xiU D : AE D) := by
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
  have hint : IsIntegral ℤ D.host.sqrtMinusD := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hsq]
    exact (isIntegral_natCast _).neg
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd0 : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hdp.ne_zero
  have h0 : D.host.sqrtMinusD ≠ 0 := fun e => by
    rw [e] at hsq
    exact hd0 (by simpa using hsq.symm)
  have hc0 : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hdT : Nat.Coprime D.host.d T := (Nat.coprime_primes hdp hT).2 hd.symm
  refine IsU.of_pres (xiU D).mul_inv ?_ ?_
  · refine UnitAt.incA_mul_mem_intAt (c := D.host.xi0) (N := ((Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℤ))
      (by rw [Int.cast_natCast]; exact UnitAt.notMem_of_coprime hv (Nat.Coprime.mul_left hc hdT)) ?_
    convert hint using 1
    rw [zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul, Host.xi0]
    field_simp
    linear_combination -hsq
  · refine UnitAt.incA_mul_mem_intAt (c := D.host.xi0⁻¹) (N := 1)
      (by rw [Int.cast_one]; exact (Ideal.ne_top_iff_one _).1 x.isPrime.ne_top) ?_
    rw [one_smul, Host.xi0, inv_div, div_neg, div_one]
    exact ((isIntegral_natCast _).mul hint).neg

/- English proof (translation)
Establish `h` using `UnitAt.latA_eq_latV (UnitAt.notMem_of_coprime hv (GlobalTheory.TwV.HalfDiffInt.absNorm_coprime D hT h2 hq hd)) (UnitAt.notMem_of_coprime hv hc) (fun a ha => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ha) (ReciprocityTheo …`. Take `⟨e, he, hg⟩` from `line_gen hζ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L).1 x`. Use `IsU.inv (fun a ha => ?_) α.inv_mul` and prove the remaining obligations. Establish `h1` using `hα L (GlobalTheory.AdelicU.frameLat L) ((incA D e * a) • ratV ζ)`. Establish `e1 : incA D e⁻¹ * incA D e = 1` using `(inU e he).inv_mul`.

Rewrite `h1` using `[h, smul_smul, hg _ (Ideal.mul_mem_left _ _ ha), hg _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha)), mul_left_comm (incA D e⁻¹) ((α⁻¹ : (AE D)ˣ) : AE D), ← mul_assoc (incA D e⁻¹), e1, one_mul]`. Conclude with `h1`.
-/
theorem isU_alpha_of_prime {x : GlobalTheory.FinPl.Pl D} {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 D.host.F) ∈ x.asIdeal) (h2 : T ∉ D.host.small)
    (hq : T ≠ D.host.q) (hd : T ≠ D.host.d) (hc : Nat.Coprime (Ideal.absNorm D.host.ccK) T)
    {L : Formalism.BasicNotions.TH.HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {α : (AE D)ˣ}
    (hα : ∀ (S : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat S) y,
      y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x)) : IsU x (α : AE D) := by
  have h := UnitAt.latA_eq_latV (UnitAt.notMem_of_coprime hv (GlobalTheory.TwV.HalfDiffInt.absNorm_coprime D hT h2 hq hd))
    (UnitAt.notMem_of_coprime hv hc) (fun a ha => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ha)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D)
  obtain ⟨e, he, hg⟩ := line_gen hζ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L).1 x
  refine IsU.inv (fun a ha => ?_) α.inv_mul
  have h1 := hα L (GlobalTheory.AdelicU.frameLat L) ((incA D e * a) • ratV ζ)
  have e1 : incA D e⁻¹ * incA D e = 1 := (inU e he).inv_mul
  rw [h, smul_smul, hg _ (Ideal.mul_mem_left _ _ ha), hg _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha)),
    mul_left_comm (incA D e⁻¹) ((α⁻¹ : (AE D)ˣ) : AE D), ← mul_assoc (incA D e⁻¹), e1, one_mul] at h1
  exact h1

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Yd cX ex W hW hr u f B k _ _ _ _ ι v o n G pl hc _ _ sh _ _ hb hp x _ hx u'' hu'' a ha`. Establish `hTp : (D.mem u'').A.T.Prime` using `(D.mem u'').A.T_prime`. Establish `hcop : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.mem u'').A.T`. Take `⟨P, hP⟩` from `exists_place D.host.E hTp`. Use `((Nat.Prime.coprime_iff_not_dvd hTp).2 fun ⟨t, ht⟩ => hW.aa P (Or.inr (Or.inr ⟨u'', hP⟩)) ?_).symm` and prove the remaining obligations.

Rewrite using `[ht, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hP`. Take `⟨α, hα⟩` from `GlobalTheory.IdeleAA.exists_idele_AA D _ hc.std`. Establish `hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE f.c.ψ (s * o) = 1) ↔ (((xiU D * α * cU α)⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x)` using `fun s hs => by`. Rewrite using `[(hα x).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]`.

Establish `uξ` using `isU_xi_of_prime hTp hu'' (D.T_ne_d u'') hcop`. Establish `uα` using `isU_alpha_of_prime hTp hu'' (UpperTheory.Small.not_mem_of_mod D.host (D.T_mod_cond u'')) (D.T_ne_q u'') (D.T_ne_d u'') hcop sh.pre.line (hα x).1`. Establish `ug : IsU x (incA D (W.S.X.B.g : D.host.E))`. Use `isU_nat (UnitAt.notMem_of_coprime hu'' ?_)` and prove the remaining obligations. Rewrite using `[W.S.X.g_eq]`.

Conclude with `Nat.Coprime.mul_left ((Nat.coprime_primes (D.host.g_prime 0) hTp).2 (D.T_ne_g u'' 0).symm) ((Nat.coprime_primes (D.host.g_prime 1) hTp).2 (D.T_ne_g u'' 1).symm)`. Establish `uc : IsU x (cU α : AE D)` using `uα.conj`. Take `⟨μ, lam, n1, n2, n3⟩` from `hb.norm`. Establish `hξ : -D.host.xi0 ^ (D.R.m / 2) ≠ 0` using `neg_ne_zero.2 (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))`. Establish `hμ : μ ≠ 0` using `left_ne_zero_of_mul (n1 ▸ hξ)`.

Establish `hlam : lam ≠ 0` using `right_ne_zero_of_mul (n1 ▸ hξ)`. Establish `h₀ : 0 + 2 * D.R.rS + 2 = D.R.m`. Take `⟨c, hc⟩` from `D.R.m_even`. Use `D.R.two_le_m` as an intermediate fact. Unfold `Ranks.rS`.

Use linear arithmetic over natural numbers and integers. Take `⟨s, hs, he⟩` from `GlobalTheory.LineIdeal.first_vec (F0 W u) (W.S.tr u) hW.bot.idE hc.std B hμ n2 ⟨0, hr⟩ rfl`. Establish `hI` using `GlobalTheory.LineIdeal.all_ideal hc sh (fun n h x hx => by subst h; exact hp x hx) (fun j hj => by`. Express the relevant statement in the definitionally equal form `0 < (D.sp.X (j + 1)).rank`. Rewrite using `[Formalism.L2.Forms.rankN D _ hj]`.

Unfold `Ranks.N`. Use `D.R.m_add_three_le_k` as an intermediate fact. Use the proof step `omega) hlam n3 hx (hα x).1 hψ 0 D.R.rS h₀ (D.R.rS - 1) ⟨0, hr⟩ (by simp only; omega)`. Establish `hd : B.d.e = (f.c.bes 0 D.R.rS h₀).d.e` using `eq_of_heq (Sigma.mk.inj (congrArg (fun Z : BesLev D D.R.rS => (⟨Z.V.rank, Z.d.e⟩ : Σ n, Matrix (Fin n) (Fin D.R.rS) D.host.E)) (hb.lev h₀))).2`. Rewrite `hI` using `[← mul_assoc (α * α), ← mul_assoc ((xiU D * α * cU α) ^ _)]`.

Establish `uK : IsU x (((xiU D * α * cU α) ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) : (AE D)ˣ) : AE D)`. Establish `h1 : IsU x (((xiU D * cU α)⁻¹ : (AE D)ˣ) : AE D)` using `(uξ.mul uc).inv (xiU D * cU α).mul_inv`. Rewrite using `[Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]`. Conclude with `(((uξ.mul uα).mul uc).pow _).mul ((uα.mul uα).mul ((uα.mul h1).pow _))`. Generalize the expression as in `(xiU D * α * cU α) ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) = K at hI uK`.

Establish `uS : IsU x (incA D (-s * (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)))`. Establish `h1 : IsU x (incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS))`. Rewrite using `[map_mul, map_pow, map_pow]`. Conclude with `(IsU.pow (u := incA D D.host.xi0) uξ _).mul (ug.pow _)`. Break down `hs with rfl | rfl` into its components or cases.

Rewrite using `[neg_one_mul, map_neg]`. Conclude with `h1.neg`. Rewrite using `[neg_neg, one_mul]` and apply the resulting hypothesis. Establish `hg0 : (W.S.X.B.g : D.host.E) ≠ 0`. Rewrite using `[W.S.X.g_eq]`.

Conclude with `Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)`. Apply the tactic sequence `have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> simp`. Take `⟨w, hw⟩ : ∃ w, w = s * (μ * (W.S.X.B.g : D.host.E) ^ D.R.rS)` from `⟨_, rfl⟩`. Establish `hw0 : w ≠ 0` using `hw ▸ mul_ne_zero hs0 (mul_ne_zero hμ (pow_ne_zero _ hg0))`. Establish `hlw : -s * (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS) = lam * w`.

Rewrite using `[hw]`. Take the linear combination `(-s * (W.S.X.B.g : D.host.E) ^ D.R.rS) * n1`. Rewrite `he` using `[← hw]`. Rewrite `uS` using `[hlw, map_mul]`. Establish `e1 : incA D w * incA D w⁻¹ = 1` using `(inU w hw0).mul_inv`.

Establish `hy : (fun i => a * incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (rank_eq W.S.X W.Q.instEq) i)))) = colMul B.d.jX ⟨0, hr⟩ (incA D w⁻¹ * a)`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `_ = _ * incA D (B.d.e i ⟨0, hr⟩)`. Rewrite using `[he, map_mul]`. Generalize the expression as in `incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (rank_eq W.S.X W.Q.instEq) i))) = t`.

Take the linear combination `(-a * t) * e1`. Establish `hj : B.d.jX = (f.c.bes 0 D.R.rS h₀).d.jX` using `congrArg rat hd`. Establish `h1` using `hI (incA D w⁻¹ * a) (Ideal.mul_mem_left _ _ ha)`. Rewrite `h1` using `[← hj]`. Use `(iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v.N 0) (· = x)) hy)).trans (h1.trans ?_)` and prove the remaining obligations.

Rewrite using `[(uK.mul uS) _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha))]`. Establish `e2` using `(K * inU lam hlam).mul_inv`. Rewrite `e2` using `[Units.val_mul, inU_val]`. Use `iff_of_eq (congrArg (· ∈ _) ?_)` and prove the remaining obligations. Take the linear combination `(incA D w * incA D w⁻¹ * a) * e2 + a * e1`.
-/
theorem lat_zero_line : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (hr : 1 ≤ D.R.rS) u (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v' : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v') (pl : Fin n ≃ (pk W).Pg), f.c.Is → v'.Is → VTie f v' → ShapeOff v' o → GPin G → GRead f G pl → BotTie f B v' o G → GlobalTheory.MiTop.PrimTop (c := f.c) v'.tP o.ζ₀ → ∀ x : GlobalTheory.FinPl.Pl D, x ∉ v'.gP → x ∉ v'.tP → ∀ u'' : D.what₂.Word, (((D.mem u'').A.T : ℕ) : 𝓞 D.host.F) ∈ x.asIdeal → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = x), ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) (v'.N 0) (· = x) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = x)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u f B k _ _ _ _ ι v o n G pl hc _ _ sh _ _ hb hp x _ hx u'' hu'' a ha
  have hTp : (D.mem u'').A.T.Prime := (D.mem u'').A.T_prime
  have hcop : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.mem u'').A.T := by
    obtain ⟨P, hP⟩ := exists_place D.host.E hTp
    refine ((Nat.Prime.coprime_iff_not_dvd hTp).2 fun ⟨t, ht⟩ => hW.aa P (Or.inr (Or.inr ⟨u'', hP⟩)) ?_).symm
    rw [ht, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hP
  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D _ hc.std
  have hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE f.c.ψ (s * o) = 1) ↔
      (((xiU D * α * cU α)⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x) := fun s hs => by
    rw [(hα x).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  have uξ := isU_xi_of_prime hTp hu'' (D.T_ne_d u'') hcop
  have uα := isU_alpha_of_prime hTp hu'' (UpperTheory.Small.not_mem_of_mod D.host (D.T_mod_cond u'')) (D.T_ne_q u'') (D.T_ne_d u'') hcop sh.pre.line (hα x).1
  have ug : IsU x (incA D (W.S.X.B.g : D.host.E)) := by
    refine isU_nat (UnitAt.notMem_of_coprime hu'' ?_)
    rw [W.S.X.g_eq]
    exact Nat.Coprime.mul_left ((Nat.coprime_primes (D.host.g_prime 0) hTp).2 (D.T_ne_g u'' 0).symm)
      ((Nat.coprime_primes (D.host.g_prime 1) hTp).2 (D.T_ne_g u'' 1).symm)
  have uc : IsU x (cU α : AE D) := uα.conj
  obtain ⟨μ, lam, n1, n2, n3⟩ := hb.norm
  have hξ : -D.host.xi0 ^ (D.R.m / 2) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (n1 ▸ hξ)
  have hlam : lam ≠ 0 := right_ne_zero_of_mul (n1 ▸ hξ)
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.rS
    omega
  obtain ⟨s, hs, he⟩ := GlobalTheory.LineIdeal.first_vec (F0 W u) (W.S.tr u) hW.bot.idE hc.std B hμ n2 ⟨0, hr⟩ rfl
  have hI := GlobalTheory.LineIdeal.all_ideal hc sh (fun n h x hx => by subst h; exact hp x hx) (fun j hj => by
      change 0 < (D.sp.X (j + 1)).rank
      rw [Formalism.L2.Forms.rankN D _ hj]
      unfold Ranks.N
      have := D.R.m_add_three_le_k
      omega) hlam n3 hx (hα x).1 hψ 0 D.R.rS h₀ (D.R.rS - 1) ⟨0, hr⟩ (by simp only; omega)
  have hd : B.d.e = (f.c.bes 0 D.R.rS h₀).d.e := eq_of_heq (Sigma.mk.inj (congrArg
    (fun Z : BesLev D D.R.rS => (⟨Z.V.rank, Z.d.e⟩ : Σ n, Matrix (Fin n) (Fin D.R.rS) D.host.E)) (hb.lev h₀))).2
  rw [← mul_assoc (α * α), ← mul_assoc ((xiU D * α * cU α) ^ _)] at hI
  have uK : IsU x (((xiU D * α * cU α) ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) : (AE D)ˣ) : AE D) := by
    have h1 : IsU x (((xiU D * cU α)⁻¹ : (AE D)ˣ) : AE D) := (uξ.mul uc).inv (xiU D * cU α).mul_inv
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    exact (((uξ.mul uα).mul uc).pow _).mul ((uα.mul uα).mul ((uα.mul h1).pow _))
  generalize (xiU D * α * cU α) ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) = K at hI uK
  have uS : IsU x (incA D (-s * (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS))) := by
    have h1 : IsU x (incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) := by
      rw [map_mul, map_pow, map_pow]
      exact (IsU.pow (u := incA D D.host.xi0) uξ _).mul (ug.pow _)
    rcases hs with rfl | rfl
    · rw [neg_one_mul, map_neg]; exact h1.neg
    · rwa [neg_neg, one_mul]
  have hg0 : (W.S.X.B.g : D.host.E) ≠ 0 := by
    rw [W.S.X.g_eq]
    exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> simp
  obtain ⟨w, hw⟩ : ∃ w, w = s * (μ * (W.S.X.B.g : D.host.E) ^ D.R.rS) := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := hw ▸ mul_ne_zero hs0 (mul_ne_zero hμ (pow_ne_zero _ hg0))
  have hlw : -s * (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS) = lam * w := by
    rw [hw]
    linear_combination (-s * (W.S.X.B.g : D.host.E) ^ D.R.rS) * n1
  rw [← hw] at he
  rw [hlw, map_mul] at uS
  have e1 : incA D w * incA D w⁻¹ = 1 := (inU w hw0).mul_inv
  have hy : (fun i => a * incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (rank_eq W.S.X W.Q.instEq) i)))) =
      colMul B.d.jX ⟨0, hr⟩ (incA D w⁻¹ * a) := by
    funext i
    change _ = _ * incA D (B.d.e i ⟨0, hr⟩)
    rw [he, map_mul]
    generalize incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (rank_eq W.S.X W.Q.instEq) i))) = t
    linear_combination (-a * t) * e1
  have hj : B.d.jX = (f.c.bes 0 D.R.rS h₀).d.jX := congrArg rat hd
  have h1 := hI (incA D w⁻¹ * a) (Ideal.mul_mem_left _ _ ha)
  rw [← hj] at h1
  refine (iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v.N 0) (· = x)) hy)).trans (h1.trans ?_)
  rw [(uK.mul uS) _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha))]
  have e2 := (K * inU lam hlam).mul_inv
  rw [Units.val_mul, inU_val] at e2
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (incA D w * incA D w⁻¹ * a) * e2 + a * e1

end GlobalTheory.LineOffT

end
