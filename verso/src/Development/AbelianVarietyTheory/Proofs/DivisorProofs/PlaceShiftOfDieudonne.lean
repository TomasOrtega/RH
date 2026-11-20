import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumEigenMultiplicity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepBasisCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsomComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEmbeddingDeterminantValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaximalIdealIffNormLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentQuotientDatumCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieNumberFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichLatticeRepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieHodgeTateKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichStarRepStatement

set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.PlaceShiftGlue

/- English proof (translation)
Introduce `h`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h1` using `IsCMField.complexEmbedding_complexConj E φ (H.rt : E)`. Rewrite `h1` using `[h]`. Establish `h2 : φ (H.rt : E) ^ 2 = -(H.d : ℂ)`.

Rewrite using `[← map_pow, RingOfIntegers.coe_eq_algebraMap, ← map_pow, H.rt_sq]`. Simplify using the standard rewrite rules. Take `⟨r, hr⟩` from `Complex.conj_eq_iff_real.1 h1.symm`. Rewrite `h2` using `[hr]`. Establish `h3 : r ^ 2 = -(H.d : ℝ)` using `by exact_mod_cast h2`.

Establish `h4 : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Use polynomial arithmetic with `[sq_nonneg r]`.
-/
theorem bar_rt_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    IsCMField.complexConj E (H.rt : E) ≠ (H.rt : E) := by
  intro h
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
  rw [h] at h1
  have h2 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, RingOfIntegers.coe_eq_algebraMap, ← map_pow, H.rt_sq]; simp
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h1.symm
  rw [hr] at h2
  have h3 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h2
  have h4 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

open Classical in

/- English proof (translation)
Use `haveI := Fintype.ofFinite ι`. Simplify using `only [finsum_eq_sum_of_fintype, mul_add, Finset.mul_sum]`. Establish `: ∑ i, (n i : ℝ) * κ i = ∑ i, (a : ℝ) * (if S i then κ i else 0) + ∑ i, (q : ℝ) * (if S i then 0 else κ i)`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hn]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_two_weights {ι : Type} [Finite ι] (S : ι → Prop) (n : ι → ℕ) (κ : ι → ℝ) (κ₀ : ℝ) (a q : ℕ)
    (hn : ∀ i, n i = if S i then a else q) :
    ((a + q : ℕ) : ℝ) * κ₀ + ∑ᶠ i, (n i : ℝ) * κ i =
      a * (κ₀ + ∑ᶠ i, if S i then κ i else 0) + q * (κ₀ + ∑ᶠ i, if S i then 0 else κ i) := by
  haveI := Fintype.ofFinite ι
  simp only [finsum_eq_sum_of_fintype, mul_add, Finset.mul_sum]
  have : ∑ i, (n i : ℝ) * κ i =
      ∑ i, (a : ℝ) * (if S i then κ i else 0) + ∑ i, (q : ℝ) * (if S i then 0 else κ i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hn]
    split_ifs <;> simp
  rw [this]
  push_cast
  ring

/- English proof (translation)
Use `haveI : Module.Free ℤ_[p] Λ := inferInstance`. Take `⟨N, -, hN, -⟩` from `GlobalTheory.DetInv.rep_free_charpoly p Λ h _ (Module.finBasis ℤ_[p] Λ) ρ`. Conclude with `⟨N, hN.trans (mul_comm _ _)⟩`.
-/
theorem exists_height_eq {p : ℕ} [Fact p.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] {h : ℕ}
    (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]) : ∃ N, h = Module.finrank ℤ_[p] Λ * N := by
  haveI : Module.Free ℤ_[p] Λ := inferInstance
  obtain ⟨N, -, hN, -⟩ := GlobalTheory.DetInv.rep_free_charpoly p Λ h _ (Module.finBasis ℤ_[p] Λ) ρ
  exact ⟨N, hN.trans (mul_comm _ _)⟩

open Classical in

/- English proof (translation)
Establish `hv` using `P.integers`. Take `⟨hT, hH, hex, heig⟩` from `GlobalTheory.T.datum_tie_number_field_point p C v O E P ε h D φ hε hD`. Take `⟨h', D', iT, pT, iM, pM, hsp⟩` from `GlobalTheory.T.idempotent_quotient_datum_compat p C v O hv ε hε _ Λ π e he hπ hk h D`. Establish `hss` using `GlobalTheory.DetInv.part_rank_dim_shift p C v O hv ε hε _ Λ π e he hπ hk h h' D D' iT pT iM pM hsp hT hH`. Take `⟨N, hN⟩` from `exists_height_eq D'.ρT`.

Take `⟨r, hr0, hr, hlog⟩` from `hκ N h' hN D'`. Establish `hdim` using `(GlobalTheory.eig_decomp_T_H p C v O hv ε hε Λ N h' hN D').1.2.2 ((γ : O →+* O).comp t₀)`. Take `⟨-, hd, hsh⟩` from `hss ((γ : O →+* O).comp t₀)`. Establish `ha : Module.finrank C (P.eigW (embO P.integers τ)) = a` using `by rw [hrank, if_pos rfl]`. Establish `hq : Module.finrank C (P.eigW ((embO P.integers τ).comp (starRingEnd (𝓞 E)))) = q`.

Rewrite using `[hτ', hrank, if_neg hrt]`. Take `⟨h1, h2, h3⟩` from `GlobalTheory.T.datum_tie_hodge_tate_kernel p C v O E P ε h D φ hε hD _ τ r (RingHom.ext hτ) (hsh r hr) a q x y g g' ha hq hx hy hg hg'`. Establish `hNa : N = a + q` using `by rw [← hdim, hd, h3]`. Use `haveI := (GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ).1`. Establish `hlie : ∀ σ : Λ →+* O, D'.lieRank ((γ : O →+* O).comp σ) = if σ (π (1 ⊗ₜ rt)) = t₀ (π (1 ⊗ₜ rt)) then a else q` using `fun σ => by`.

Take `⟨ψ, hψ⟩` from `hex (((γ : O →+* O).comp σ).comp (π : ℤ_[p] ⊗[ℤ] 𝓞 E →+* Λ))`. Rewrite using `[(hss _).1, (heig _ ψ hψ).2.2.2, hrank]`. Establish `e1 : γ (σ (π (1 ⊗ₜ rt))) = embO P.integers ψ rt` using `RingHom.congr_fun hψ rt`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Rewrite using `[← algebraMap_embO P.integers ψ, ← algebraMap_embO P.integers τ, ← e1, ← hτ, hv.hom_inj.eq_iff, γ.injective.eq_iff]`.

Establish `hg0 : ((v g'.det : NNReal) : ℝ) ≠ 0`. Conclude with `(Valuation.ne_zero_iff v).2 h2` after adjusting the coercions. Establish `hr0' : (r : ℝ) ≠ 0` using `by exact_mod_cast hr0`. Rewrite using `[h1, NNReal.coe_mul, Real.log_mul hr0' hg0, add_sub_cancel_right, hlog, hNa]`. Conclude with `sum_two_weights _ (fun σ => D'.lieRank ((γ : O →+* O).comp σ)) κ κ₀ a q hlie`.
-/
theorem shift_at_point (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (root ε).untilt p) (h : ℕ) (D : Datum ε h (ℤ_[p] ⊗[ℤ] 𝓞 E))
    (φ : P.V ≃ₗ[C] (Fin h → C))
    (hD : IsTie P D (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom φ)
    (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ]
    [FaithfulSMul ℤ_[p] Λ] (π : ℤ_[p] ⊗[ℤ] 𝓞 E →ₐ[ℤ_[p]] Λ) (e : ℤ_[p] ⊗[ℤ] 𝓞 E) (he : IsIdempotentElem e)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = Ideal.span {1 - e}) (t₀ : Λ →+* O) (γ : O ≃+* O)
    (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ)
    (hκ : ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ), ∃ r : NNReal, r ≠ 0 ∧
      IsShift C v D ((γ : O →+* O).comp t₀) r ∧
      Real.log r = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ)
    (τ τ' : E →+* C) (hτ : ∀ a : 𝓞 E, γ (t₀ (π (1 ⊗ₜ a))) = embO P.integers τ a)
    (hτ' : (embO P.integers τ).comp (starRingEnd (𝓞 E)) = embO P.integers τ')
    (rt : 𝓞 E) (hrt : τ' (rt : E) ≠ τ (rt : E)) (a q : ℕ)
    (hrank : ∀ ψ : E →+* C, Module.finrank C (P.eigW (embO P.integers ψ)) =
      if ψ (rt : E) = τ (rt : E) then a else q)
    (x : Fin a → P.V) (y : Fin q → P.V) (g : Matrix (Fin a) (Fin a) C) (g' : Matrix (Fin q) (Fin q) C)
    (hx : Submodule.span O (Set.range x) = P.wRec (embO P.integers τ))
    (hy : Submodule.span O (Set.range y) = P.wRec ((embO P.integers τ).comp (starRingEnd (𝓞 E))))
    (hg : IsLatBasis C (P.latTQuot (σ := fun φ' : E →+* C => embO P.integers φ') (isSplitting_embO P.integers) τ)
      (fun i => ∑ j, g i j • x j))
    (hg' : IsLatBasis C (P.latTSub ((embO P.integers τ).comp (starRingEnd (𝓞 E)))) (fun i => ∑ j, g' i j • y j)) :
    Real.log (v g.det) - Real.log (v g'.det) =
      a * (κ₀ + ∑ᶠ σ : Λ →+* O, if σ (π (1 ⊗ₜ rt)) = t₀ (π (1 ⊗ₜ rt)) then κ σ else 0) +
      q * (κ₀ + ∑ᶠ σ : Λ →+* O, if σ (π (1 ⊗ₜ rt)) = t₀ (π (1 ⊗ₜ rt)) then 0 else κ σ) := by
  have hv := P.integers
  obtain ⟨hT, hH, hex, heig⟩ := GlobalTheory.T.datum_tie_number_field_point p C v O E P ε h D φ hε hD
  obtain ⟨h', D', iT, pT, iM, pM, hsp⟩ := GlobalTheory.T.idempotent_quotient_datum_compat p C v O hv ε hε _ Λ π e he hπ hk h D
  have hss := GlobalTheory.DetInv.part_rank_dim_shift p C v O hv ε hε _ Λ π e he hπ hk h h' D D' iT pT iM pM hsp hT hH
  obtain ⟨N, hN⟩ := exists_height_eq D'.ρT
  obtain ⟨r, hr0, hr, hlog⟩ := hκ N h' hN D'
  have hdim := (GlobalTheory.eig_decomp_T_H p C v O hv ε hε Λ N h' hN D').1.2.2 ((γ : O →+* O).comp t₀)
  obtain ⟨-, hd, hsh⟩ := hss ((γ : O →+* O).comp t₀)
  have ha : Module.finrank C (P.eigW (embO P.integers τ)) = a := by rw [hrank, if_pos rfl]
  have hq : Module.finrank C (P.eigW ((embO P.integers τ).comp (starRingEnd (𝓞 E)))) = q := by
    rw [hτ', hrank, if_neg hrt]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.datum_tie_hodge_tate_kernel p C v O E P ε h D φ hε hD _ τ r (RingHom.ext hτ) (hsh r hr) a q x y g g'
    ha hq hx hy hg hg'
  have hNa : N = a + q := by rw [← hdim, hd, h3]
  haveI := (GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ).1
  have hlie : ∀ σ : Λ →+* O, D'.lieRank ((γ : O →+* O).comp σ) =
      if σ (π (1 ⊗ₜ rt)) = t₀ (π (1 ⊗ₜ rt)) then a else q := fun σ => by
    obtain ⟨ψ, hψ⟩ := hex (((γ : O →+* O).comp σ).comp (π : ℤ_[p] ⊗[ℤ] 𝓞 E →+* Λ))
    rw [(hss _).1, (heig _ ψ hψ).2.2.2, hrank]
    have e1 : γ (σ (π (1 ⊗ₜ rt))) = embO P.integers ψ rt := RingHom.congr_fun hψ rt
    refine if_congr ?_ rfl rfl
    rw [← algebraMap_embO P.integers ψ, ← algebraMap_embO P.integers τ, ← e1, ← hτ,
      hv.hom_inj.eq_iff, γ.injective.eq_iff]
  have hg0 : ((v g'.det : NNReal) : ℝ) ≠ 0 := by
    exact_mod_cast (Valuation.ne_zero_iff v).2 h2
  have hr0' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
  rw [h1, NNReal.coe_mul, Real.log_mul hr0' hg0, add_sub_cancel_right, hlog, hNa]
  exact sum_two_weights _ (fun σ => D'.lieRank ((γ : O →+* O).comp σ)) κ κ₀ a q hlie

/- English proof (translation)
Introduce `E _ _ _ H _ ℓ _ w`. Distinguish the cases in `hw : ∃ τ₀ : E →+* ℂ_[ℓ], ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ ‖τ₀ (a : E)‖ < 1`. Use `swap`. Conclude with `⟨0, 0, fun τ hτ => (hw ⟨τ, hτ⟩).elim⟩`. Take `⟨τ₀, hτ₀⟩` from `hw`.

Take `⟨i1, i2, ε, hv, hε⟩` from `PadicComplexHost.main ℓ`. Take `⟨Λ, _, _, _, _, _, _, π, e, t₀, he, hπ, hk, ht₀, hall⟩` from `GlobalTheory.PlaceRing.exists_placeRing E ℓ (embO hv τ₀)`. Take `⟨κ₀, κ, hκ⟩` from `GlobalTheory.T.dvr_embedding_determinant_value ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] hv ε hε Λ t₀`. Use `⟨κ₀ + ∑ᶠ σ : Λ →+* 𝓞_ℂ_[ℓ], @ite ℝ (σ (π (1 ⊗ₜ H.rt)) = t₀ (π (1 ⊗ₜ H.rt))) (Classical.propDecidable _) (κ σ) 0, κ₀ + ∑ᶠ σ : Λ →+* 𝓞_ℂ_[ℓ], @ite ℝ (σ (π (1 ⊗ₜ H.rt)) = t₀ (π (1 ⊗ₜ H.rt))) (Classical.propDecidable _) 0 (κ σ), fun τ hτ => ?_⟩` and prove the remaining obligations. Use `letI := H.starRing`.

Use `letI := algPadicInt ℓ`. Use `letI := algPadicField ℓ`. Use `haveI := towerPadic ℓ`. Introduce `_ P a q hrank x x' g g' hx hx' hg hg'`. Establish `hc : ∀ (ψ : E →+* ℂ_[ℓ]) (b : 𝓞 E), ((embO hv ψ b : 𝓞_ℂ_[ℓ]) : ℂ_[ℓ]) = ψ b` using `fun ψ b => algebraMap_embO hv ψ b`.

Take `⟨t, ht⟩` from `hall (embO hv τ) fun b => by rw [hc, hc, ← hτ, ← hτ₀]`. Take `⟨γ, hγ, rfl⟩` from `GlobalTheory.EmbConj.exists_isIsom_comp ℓ Λ t₀ t`. Establish `hε' : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε` using `Dieudonne.isPrimitiveRoot_untilt_root hε`. Establish `hS` using `GlobalTheory.T.hodgeTateSandwich_of_prismaticDieudonne hPD ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] hv ε hε'`. Establish `hP` using `(hK ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] (𝓞 E) P).2.2.2`.

Take `⟨h, D, φ, hD⟩` from `GlobalTheory.T.hodge_tate_sandwich_star_rep ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] ε hε' hS (𝓞 E) P hP (GlobalTheory.T.hodge_tate_sandwich_lattice_rep hSW ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] ε hε' hS (𝓞 E) P hP)`. Rewrite using `[← PadicComplexHost.valuation_coe_eq_norm, ← PadicComplexHost.valuation_coe_eq_norm]`. Use `shift_at_point ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] E P ε hε h D φ hD Λ π e he hπ hk t₀ γ κ₀ κ (hκ γ hγ) τ (τ.comp (IsCMField.complexConj E).toAlgHom.toRingHom) ht ?_ H.rt ?_ a q hrank _ _ g g' hx hx' hg hg'` and prove the remaining obligations. Use `RingHom.ext fun b => hv.hom_inj ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, algebraMap_embO, algebraMap_embO]`.

Conclude with `congrArg τ (H.bar_eq b)`. Conclude with `fun h0 => bar_rt_ne H (τ.injective h0)`.
-/
theorem placeShift (hSW : GlobalTheory.Published.ScholzeWeinsteinB) (hPD : GlobalTheory.Published.PrismaticDieudonneHodge)
    (hK : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint) : GlobalTheory.FlatCM.PlaceShiftSt := by
  classical
  intro E _ _ _ H _ ℓ _ w
  by_cases hw : ∃ τ₀ : E →+* ℂ_[ℓ], ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ ‖τ₀ (a : E)‖ < 1
  swap
  · exact ⟨0, 0, fun τ hτ => (hw ⟨τ, hτ⟩).elim⟩
  obtain ⟨τ₀, hτ₀⟩ := hw
  obtain ⟨i1, i2, ε, hv, hε⟩ := PadicComplexHost.main ℓ
  obtain ⟨Λ, _, _, _, _, _, _, π, e, t₀, he, hπ, hk, ht₀, hall⟩ := GlobalTheory.PlaceRing.exists_placeRing E ℓ (embO hv τ₀)
  obtain ⟨κ₀, κ, hκ⟩ := GlobalTheory.T.dvr_embedding_determinant_value ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] hv ε hε Λ t₀
  refine ⟨κ₀ + ∑ᶠ σ : Λ →+* 𝓞_ℂ_[ℓ],
      @ite ℝ (σ (π (1 ⊗ₜ H.rt)) = t₀ (π (1 ⊗ₜ H.rt))) (Classical.propDecidable _) (κ σ) 0,
    κ₀ + ∑ᶠ σ : Λ →+* 𝓞_ℂ_[ℓ],
      @ite ℝ (σ (π (1 ⊗ₜ H.rt)) = t₀ (π (1 ⊗ₜ H.rt))) (Classical.propDecidable _) 0 (κ σ), fun τ hτ => ?_⟩
  letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ
  intro _ P a q hrank x x' g g' hx hx' hg hg'
  have hc : ∀ (ψ : E →+* ℂ_[ℓ]) (b : 𝓞 E), ((embO hv ψ b : 𝓞_ℂ_[ℓ]) : ℂ_[ℓ]) = ψ b := fun ψ b =>
    algebraMap_embO hv ψ b
  obtain ⟨t, ht⟩ := hall (embO hv τ) fun b => by rw [hc, hc, ← hτ, ← hτ₀]
  obtain ⟨γ, hγ, rfl⟩ := GlobalTheory.EmbConj.exists_isIsom_comp ℓ Λ t₀ t
  have hε' : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε := Dieudonne.isPrimitiveRoot_untilt_root hε
  have hS := GlobalTheory.T.hodgeTateSandwich_of_prismaticDieudonne hPD ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] hv ε hε'
  have hP := (hK ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] (𝓞 E) P).2.2.2
  obtain ⟨h, D, φ, hD⟩ := GlobalTheory.T.hodge_tate_sandwich_star_rep ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] ε hε' hS (𝓞 E) P hP
    (GlobalTheory.T.hodge_tate_sandwich_lattice_rep hSW ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] ε hε' hS (𝓞 E) P hP)
  rw [← PadicComplexHost.valuation_coe_eq_norm, ← PadicComplexHost.valuation_coe_eq_norm]
  refine shift_at_point ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] E P ε hε h D φ hD Λ π e he hπ hk t₀ γ κ₀ κ (hκ γ hγ)
    τ (τ.comp (IsCMField.complexConj E).toAlgHom.toRingHom) ht ?_ H.rt ?_ a q hrank _ _ g g' hx hx' hg hg'
  · refine RingHom.ext fun b => hv.hom_inj ?_
    rw [RingHom.comp_apply, algebraMap_embO, algebraMap_embO]
    exact congrArg τ (H.bar_eq b)
  · exact fun h0 => bar_rt_ne H (τ.injective h0)

end GlobalTheory.PlaceShiftGlue

end
