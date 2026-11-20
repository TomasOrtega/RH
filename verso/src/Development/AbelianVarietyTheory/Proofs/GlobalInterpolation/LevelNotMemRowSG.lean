import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrdDetConjFinite
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitOfConjPNe

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.MuOffMove

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S}

/- English proof (translation)
Unfold `ordDet frameAt`. Rewrite using `[h]`.
-/
theorem ordDet_congr {E : Type} [Field E] [NumberField E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {N₁ N₂ : Submodule (𝓞 E) (Sp E n)} (h : localization₂ P.asIdeal N₁ = localization₂ P.asIdeal N₂) : ordDet P N₁ = ordDet P N₂ := by
  unfold ordDet frameAt
  rw [h]

/- English proof (translation)
Use extensionality with `r`. Establish `e : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r` using `RingOfIntegers.ext (hX.star_F (r : X.F))`. Rewrite using `[Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, e]`.
-/
theorem under_conjP (hX : X.Ok) (Q : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime₂ Q).asIdeal.under (𝓞 X.F) = Q.asIdeal.under (𝓞 X.F) := by
  ext r
  have e : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r :=
    RingOfIntegers.ext (hX.star_F (r : X.F))
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, e]

/- English proof (translation)
Rewrite using `[Ideal.under_def, Ideal.mem_comap, map_natCast]`.
-/
theorem natCast_mem_under (Q : HeightOneSpectrum (𝓞 X.E)) (p : ℕ) :
    ((p : ℕ) : 𝓞 X.F) ∈ Q.asIdeal.under (𝓞 X.F) ↔ ((p : ℕ) : 𝓞 X.E) ∈ Q.asIdeal := by
  rw [Ideal.under_def, Ideal.mem_comap, map_natCast]

/- English proof (translation)
Unfold `QE at h`. Use `split_ifs at h with h2`. Take `⟨v, hv, e⟩` from `Finset.mem_image.1 h`. Establish `hv1 : v ∈ Qprime (mu : Chr X.F X.E X.K)` using `by simpa using hv`. Use `⟨v, ?_, e⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hn`. Establish `h4` using `(Subgroup.mem_inf.1 mu.2).2`. Conclude with `hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) hn)`. Simplify using `at h`.
-/
theorem good_of_mem_QE {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    ∃ v, GoodPl X.E S v ∧ sel v = P := by
  classical
  unfold QE at h
  split_ifs at h with h2
  · obtain ⟨v, hv, e⟩ := Finset.mem_image.1 h
    have hv1 : v ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv
    refine ⟨v, ?_, e⟩
    by_contra hn
    have h4 := (Subgroup.mem_inf.1 mu.2).2
    exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) hn)
  · simp at h

/- English proof (translation)
Introduce `hm`. Take `⟨v, hgood, e⟩` from `good_of_mem_QE h`. Establish `h5 : (l : 𝓞 X.F) ∈ v.asIdeal`. Rewrite using `[← hsel v, e, Ideal.under_def, Ideal.mem_comap, map_natCast]`. Conclude with `hm`.

Apply `hgood.2.2` to reduce the goal to its premises. Establish `h6 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ l`. Rewrite using `[← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `h5`. Use `haveI := v.isPrime`.

Break down `(Nat.dvd_prime hl).1 h6 with h7 | h7` into its components or cases. Conclude with `absurd h7 CharP.ringChar_ne_one`. Express the relevant statement in the definitionally equal form `ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S`. Rewrite using `[h7]`. Conclude with `hS`.
-/
theorem notMem_of_mem_QE (hsel : IsSel X sel) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K))
    {l : ℕ} (hl : l.Prime) (hS : l ∈ S) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨v, hgood, e⟩ := good_of_mem_QE h
  have h5 : (l : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v, e, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hm
  apply hgood.2.2
  have h6 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ l := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h5
  haveI := v.isPrime
  rcases (Nat.dvd_prime hl).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · change ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
    rw [h7]
    exact hS

/- English proof (translation)
Break down `Finset.mem_union.1 hP with h | h` into its components or cases. Conclude with `T_notMem_vGs hPr u ⟨P, h⟩`. Conclude with `notMem_of_mem_QE hsel h (hPr.T_prime u) hS`.
-/
theorem level_notMem_rowSG (hPr : Pr.Ok) (hsel : IsSel X sel) {u : Pr.Word} (hS : Pr.T u ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : (Pr.T u : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  rcases Finset.mem_union.1 hP with h | h
  · exact T_notMem_vGs hPr u ⟨P, h⟩
  · exact notMem_of_mem_QE hsel h (hPr.T_prime u) hS

/- English proof (translation)
Establish `h0 : Pr.piT u ≠ 0`. Use `left_ne_zero_of_mul (b := X.conjO (Pr.piT u)) ?_` and prove the remaining obligations. Rewrite using `[hPr.piT_norm u]`. Conclude with `(hPr.T_prime u).ne_zero` after adjusting the coercions. Use `⟨decoFin_mem_of_mem_divs, fun h => ?_⟩` and prove the remaining obligations.

Unfold `Primes.vT divs`. Establish `hf : {P : HeightOneSpectrum (𝓞 X.E) | Pr.piT u ∈ P.asIdeal}.Finite`. Use `(Ideal.finite_factors (I := Ideal.span {Pr.piT u}) (by simpa using h0)).subset fun Q hQ => ?_` and prove the remaining obligations. Conclude with `Ideal.dvd_span_singleton.2 hQ`. Rewrite using `[dif_pos hf]`.

Simplify using `using h`.
-/
theorem mem_vT (hPr : Pr.Ok) (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) : P ∈ Pr.vT u ↔ Pr.piT u ∈ P.asIdeal := by
  have h0 : Pr.piT u ≠ 0 := by
    refine left_ne_zero_of_mul (b := X.conjO (Pr.piT u)) ?_
    rw [hPr.piT_norm u]
    exact_mod_cast (hPr.T_prime u).ne_zero
  refine ⟨decoFin_mem_of_mem_divs, fun h => ?_⟩
  unfold Primes.vT divs
  have hf : {P : HeightOneSpectrum (𝓞 X.E) | Pr.piT u ∈ P.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {Pr.piT u}) (by simpa using h0)).subset fun Q hQ => ?_
    exact Ideal.dvd_span_singleton.2 hQ
  rw [dif_pos hf]
  simpa using h

/- English proof (translation)
Introduce `h` and use `conj_piT_notMem hPr u ⟨P, hP⟩ ((mem_conjP _ _).1 ((mem_vT hPr u _).1 h))`.
-/
theorem conjP_notMem_vT (hPr : Pr.Ok) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vT u) : conjPrime₂ P ∉ Pr.vT u :=
  fun h => conj_piT_notMem hPr u ⟨P, hP⟩ ((mem_conjP _ _).1 ((mem_vT hPr u _).1 h))

open Classical in

def term (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (v : HeightOneSpectrum (𝓞 X.F)) : X.K :=
  if ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal then 1 else ((mU (sel v) ^ ordDet (sel v) N : X.Kˣ) : X.K)

/- English proof (translation)
Establish `hinj : Function.Injective sel` using `fun v w h => HeightOneSpectrum.ext (by rw [← hsel v, h, hsel w])`. Use `((GlobalTheory.OrdDetConj.ordDet_conj_finite X.E n N hN).2.preimage hinj.injOn).subset fun v hv h0 => hv ?_` and prove the remaining obligations. Unfold `term`. Use `split_ifs`. Both sides reduce to the same expression.

Rewrite using `[h0, zpow_zero, Units.val_one]`.
-/
theorem term_finite (hsel : IsSel X sel) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    (Function.mulSupport (term sel SB mU N)).Finite := by
  have hinj : Function.Injective sel := fun v w h => HeightOneSpectrum.ext (by rw [← hsel v, h, hsel w])
  refine ((GlobalTheory.OrdDetConj.ordDet_conj_finite X.E n N hN).2.preimage hinj.injOn).subset fun v hv h0 => hv ?_
  unfold term
  split_ifs
  · rfl
  · rw [h0, zpow_zero, Units.val_one]

open Classical in
/- English proof (translation)
Distinguish the cases in `hv : ∃ P ∈ Pr.vT u, P.under (𝓞 X.F) = v`. Take `⟨P, hP, hPv⟩` from `hv`. Establish `hPv' : P.asIdeal.under (𝓞 X.F) = v.asIdeal` using `congrArg HeightOneSpectrum.asIdeal hPv`. Establish `hc` using `conjP_notMem_vT hPr hP`. Establish `hsp` using `(split_of_conj_ne₂ X P v hX (fun e => hc (e.symm ▸ hP)) hPv').2`.

Establish `hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = {P}`. Use extensionality with `Q`. Rewrite using `[Finset.mem_filter, Finset.mem_singleton]`. Use `⟨fun ⟨hQ, hQv⟩ => ?_, fun e => e ▸ ⟨hP, hPv⟩⟩` and prove the remaining obligations. Conclude with `((hsp Q).1 (congrArg HeightOneSpectrum.asIdeal hQv)).resolve_right fun e => hc (e ▸ hQ)`.

Establish `hno : ¬ ∃ Q ∈ rowSG Pr sel mu, Q.asIdeal.under (𝓞 X.F) = v.asIdeal`. Introduce and unpack `⟨Q, hQ, hQv⟩`. Use `level_notMem_rowSG hPr hsel hS hQ ?_` and prove the remaining obligations. Rewrite using `[← natCast_mem_under, hQv, ← hPv', natCast_mem_under]`. Conclude with `T_mem hPr u ⟨P, hP⟩`.

Unfold `term`. Rewrite using `[hfil, Finset.prod_singleton, if_neg hno, if_neg hno, ← Units.val_mul]`. Use `congr 1`. Unfold `idxExp`. Break down `(hsp (sel v)).1 (hsel v) with e | e` into its components or cases.

Rewrite using `[e, ← zpow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hU P hP, GlobalTheory.OrdDetConj.ordDet_conjP h₁, GlobalTheory.OrdDetConj.ordDet_conjP h₂, inv_zpow', inv_zpow', ← zpow_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = ∅` using `Finset.filter_eq_empty_iff.2 fun Q hQ e => hv ⟨Q, hQ, e⟩`. Establish `hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ (sel v).asIdeal`. Introduce `h`. Rewrite `h` using `[← hPr.piT_norm u]`.

Break down `(sel v).isPrime.mem_or_mem h with h | h` into its components or cases. Conclude with `hv ⟨sel v, (mem_vT hPr u _).2 h, HeightOneSpectrum.ext (hsel v)⟩`. Conclude with `hv ⟨conjPrime₂ (sel v), (mem_vT hPr u _).2 ((mem_conjP _ _).2 h), HeightOneSpectrum.ext ((under_conjP hX _).trans (hsel v))⟩`. Unfold `term`. Rewrite using `[hfil, Finset.prod_empty, one_mul, ordDet_congr (hA _ hT)]`.
-/
theorem term_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {u : Pr.Word} (hS : Pr.T u ∈ S)
    {mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ} (hU : ∀ P ∈ Pr.vT u, mU (conjPrime₂ P) = (mU P)⁻¹) {n : ℕ}
    {N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E n)} (h₁ : IsSdLat N₁) (h₂ : IsSdLat N₂) (hA : AgreeOff (Pr.T u) N₁ N₂)
    (v : HeightOneSpectrum (𝓞 X.F)) :
    term sel (rowSG Pr sel mu) mU N₁ v =
      (∏ P ∈ Pr.vT u with P.under (𝓞 X.F) = v, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) * term sel (rowSG Pr sel mu) mU N₂ v := by
  by_cases hv : ∃ P ∈ Pr.vT u, P.under (𝓞 X.F) = v
  · obtain ⟨P, hP, hPv⟩ := hv
    have hPv' : P.asIdeal.under (𝓞 X.F) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal hPv
    have hc := conjP_notMem_vT hPr hP
    have hsp := (split_of_conj_ne₂ X P v hX (fun e => hc (e.symm ▸ hP)) hPv').2
    have hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = {P} := by
      ext Q
      rw [Finset.mem_filter, Finset.mem_singleton]
      refine ⟨fun ⟨hQ, hQv⟩ => ?_, fun e => e ▸ ⟨hP, hPv⟩⟩
      exact ((hsp Q).1 (congrArg HeightOneSpectrum.asIdeal hQv)).resolve_right fun e => hc (e ▸ hQ)
    have hno : ¬ ∃ Q ∈ rowSG Pr sel mu, Q.asIdeal.under (𝓞 X.F) = v.asIdeal := by
      rintro ⟨Q, hQ, hQv⟩
      refine level_notMem_rowSG hPr hsel hS hQ ?_
      rw [← natCast_mem_under, hQv, ← hPv', natCast_mem_under]
      exact T_mem hPr u ⟨P, hP⟩
    unfold term
    rw [hfil, Finset.prod_singleton, if_neg hno, if_neg hno, ← Units.val_mul]
    congr 1
    unfold idxExp
    rcases (hsp (sel v)).1 (hsel v) with e | e
    · rw [e, ← zpow_add]
      congr 1
      ring
    · rw [e, hU P hP, GlobalTheory.OrdDetConj.ordDet_conjP h₁, GlobalTheory.OrdDetConj.ordDet_conjP h₂, inv_zpow', inv_zpow', ← zpow_add]
      congr 1
      ring
  · have hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun Q hQ e => hv ⟨Q, hQ, e⟩
    have hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ (sel v).asIdeal := by
      intro h
      rw [← hPr.piT_norm u] at h
      rcases (sel v).isPrime.mem_or_mem h with h | h
      · exact hv ⟨sel v, (mem_vT hPr u _).2 h, HeightOneSpectrum.ext (hsel v)⟩
      · exact hv ⟨conjPrime₂ (sel v), (mem_vT hPr u _).2 ((mem_conjP _ _).2 h),
          HeightOneSpectrum.ext ((under_conjP hX _).trans (hsel v))⟩
    unfold term
    rw [hfil, Finset.prod_empty, one_mul, ordDet_congr (hA _ hT)]

/- English proof (translation)
Introduce `X Pr sel S mu u mU n N₁ N₂ hX hPr hsel hS _ hU h₁ h₂ hA`. Express the relevant statement in the definitionally equal form `∏ᶠ v, term sel (rowSG Pr sel mu) mU N₁ v = _ * ∏ᶠ v, term sel (rowSG Pr sel mu) mU N₂ v`. Establish `hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 X.F) => ∏ P ∈ Pr.vT u with P.under (𝓞 X.F) = v, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) ⊆ ((Pr.vT u).image fun P => P.under (𝓞 X.F) : Finset _)`. Introduce `v hv`. Assume the negation of the conclusion as `hn`.

Apply `hv` to reduce the goal to its premises. Use `Finset.prod_eq_one fun P hP => absurd ?_ hn` and prove the remaining obligations. Rewrite `hP` using `[Finset.mem_filter]`. Conclude with `Finset.mem_coe.2 (Finset.mem_image.2 ⟨P, hP.1, hP.2⟩)`. Rewrite using `[finprod_congr (term_eq (mu := mu) hX hPr hsel hS hU h₁ h₂ hA), finprod_mul_distrib ((Finset.finite_toSet _).subset hsub) (term_finite hsel _ mU h₂), finprod_eq_prod_of_mulSupport_subset _ hsub, Finset.prod_fiberwise_of_maps_to (g := fun P : HeightOneSpectrum (𝓞 X.E) => P.under ( …`.
-/
theorem muOff_move : ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (u : Pr.Word) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (n : ℕ) (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E n)), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → (∀ P ∈ Pr.vT u, mU (conjPrime₂ P) = (mU P)⁻¹) → IsSdLat N₁ → IsSdLat N₂ → AgreeOff (Pr.T u) N₁ N₂ → muOff sel (rowSG Pr sel mu) mU N₁ = (∏ P ∈ Pr.vT u, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) * muOff sel (rowSG Pr sel mu) mU N₂ := by
  intro X Pr sel S mu u mU n N₁ N₂ hX hPr hsel hS _ hU h₁ h₂ hA
  classical
  change ∏ᶠ v, term sel (rowSG Pr sel mu) mU N₁ v = _ * ∏ᶠ v, term sel (rowSG Pr sel mu) mU N₂ v
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 X.F) =>
      ∏ P ∈ Pr.vT u with P.under (𝓞 X.F) = v, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) ⊆
      ((Pr.vT u).image fun P => P.under (𝓞 X.F) : Finset _) := by
    intro v hv
    by_contra hn
    apply hv
    refine Finset.prod_eq_one fun P hP => absurd ?_ hn
    rw [Finset.mem_filter] at hP
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨P, hP.1, hP.2⟩)
  rw [finprod_congr (term_eq (mu := mu) hX hPr hsel hS hU h₁ h₂ hA),
    finprod_mul_distrib ((Finset.finite_toSet _).subset hsub) (term_finite hsel _ mU h₂),
    finprod_eq_prod_of_mulSupport_subset _ hsub,
    Finset.prod_fiberwise_of_maps_to (g := fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F))
      fun P hP => Finset.mem_image_of_mem (fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F)) hP]

end GlobalTheory.MuOffMove
