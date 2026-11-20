import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `hTy hShape hActs hFact hTfAct hTfCen hTEig hAt hFac hJ hc E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok`. Take `⟨h0, h1, h2, -⟩` from `hTy E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok`. Use `⟨fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h)), h0, h1, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Use `h2 g hg` as an intermediate fact.

Rewrite using `[th_eq F]`. Conclude with `this`. Introduce `g θ hs`. Take `⟨-, hcase⟩` from `hShape E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok g θ hs`. Establish `hA` using `hActs E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok g θ hs`.

Break down `hcase with ⟨hd, hk, rfl⟩ | ⟨w, t, z, i, B, hfree, hap, hi, hT, hz, hB, hzp, hh, hcen, -, hLf, rfl⟩` into its components or cases. Establish `h3` using `(hA.2.1 hd hk).2.2 _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1`. Rewrite using `[h3]`. Use function extensionality and compare the values at `a`. Establish `h4` using `hTfCen _ _ Ty 1 ⟨fun _ => by simp, map_one _⟩ _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1 a`.

Simplify using `only [Pi.smul_apply, one_smul]`. Rewrite using `[h4, mul_one]`. Take `⟨hLK, hLA⟩` from `(hFact E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok).2.1 w hfree.2.1 hfree.2.2.1 hap`. Establish `hAc` using `hA.2.2 _ (L w) _ t⁻¹ (F.j (z ^ i)⁻¹) hLK hLf hLA hcen hh`. Establish `h3` using `hAc.2.2 _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1`.

Establish `hsz : F.tr.sec (F.j (z ^ i)⁻¹) = (z ^ i)⁻¹`. Apply `(hJ E A n p S F.tr.toAdT F.tr.μ F.tr.mu F.tr.a F.tr.j F.tr.j_mx).1` to reduce the goal to its premises. Introduce `u`. Distinguish the cases in `hu : (p : 𝓞 E) ∈ u.asIdeal`. Rewrite using `[F.tr.sec_p _ u hu]`.

Simplify using `[hzp u hu]`. Conclude with `(F.tr.j_eq _ _).1 (by rw [F.tr.j_sec, F.j_tr]) u hu`. Establish `hsl : ∀ y, F.tr.sec ((L w).loc y) = CertificateRingHomMap.loc w.2.1 y`. Introduce `y`. Establish `hL : L w = fac F.tr hc w` using `(hFac E A n p S F hc w).2 _ (hok.fac w)`.

Rewrite using `[hL]`. Conclude with `(hAt E A n p S F.tr hc w.1 w.2.1 w.2.2).1 y`. Rewrite using `[h3, hh]`. Use function extensionality and compare the values at `a`. Establish `h4` using `hTfAct _ _ _ Ty (L w) _ hLK hLA t⁻¹ (F.j (z ^ i)⁻¹) hcen _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1 a`.

Establish `h5` using `hTEig E n hodd.pos x U w₀ Up V w.1 w.2.1 hfree i hi t hT z hz B hB (F.tr.sec a)`. Simplify using `only [Pi.smul_apply]`. Rewrite using `[h4, mul_smul, ← h5]`. Use `congr 1`. Use `finsum_congr fun y => ?_` and prove the remaining obligations.

Simplify using `only [map_mul, hsz, hsl]`.
-/
theorem UpperTheory.Gal.W2.Seed.pPhiEx :
    PhiTy → SeenShape → SeenActs → TyFact → TfAct → TfCen → TEig → AtApart → FacEq → JEq → UpperTheory.Gal.W2.Seed.LocComm → PhiEx := by
  intro hTy hShape hActs hFact hTfAct hTfCen hTEig hAt hFac hJ hc E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok
  obtain ⟨h0, h1, h2, -⟩ := hTy E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok
  refine ⟨fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h)), h0, h1, ?_, ?_⟩
  · intro g hg
    have := h2 g hg
    rw [th_eq F]
    exact this
  · intro g θ hs
    obtain ⟨-, hcase⟩ := hShape E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok g θ hs
    have hA := hActs E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok g θ hs
    rcases hcase with ⟨hd, hk, rfl⟩ | ⟨w, t, z, i, B, hfree, hap, hi, hT, hz, hB, hzp, hh, hcen, -, hLf, rfl⟩
    · have h3 := (hA.2.1 hd hk).2.2 _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1
      rw [h3]
      funext a
      have h4 := hTfCen _ _ Ty 1 ⟨fun _ => by simp, map_one _⟩ _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1 a
      simp only [Pi.smul_apply, one_smul]
      rw [h4, mul_one]
    · obtain ⟨hLK, hLA⟩ := (hFact E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok).2.1 w
        hfree.2.1 hfree.2.2.1 hap
      have hAc := hA.2.2 _ (L w) _ t⁻¹ (F.j (z ^ i)⁻¹) hLK hLf hLA hcen hh
      have h3 := hAc.2.2 _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1
      have hsz : F.tr.sec (F.j (z ^ i)⁻¹) = (z ^ i)⁻¹ := by
        apply (hJ E A n p S F.tr.toAdT F.tr.μ F.tr.mu F.tr.a F.tr.j F.tr.j_mx).1
        intro u
        by_cases hu : (p : 𝓞 E) ∈ u.asIdeal
        · rw [F.tr.sec_p _ u hu]
          simp [hzp u hu]
        · exact (F.tr.j_eq _ _).1 (by rw [F.tr.j_sec, F.j_tr]) u hu
      have hsl : ∀ y, F.tr.sec ((L w).loc y) = CertificateRingHomMap.loc w.2.1 y := by
        intro y
        have hL : L w = fac F.tr hc w := (hFac E A n p S F hc w).2 _ (hok.fac w)
        rw [hL]
        exact (hAt E A n p S F.tr hc w.1 w.2.1 w.2.2).1 y
      rw [h3, hh]
      funext a
      have h4 := hTfAct _ _ _ Ty (L w) _ hLK hLA t⁻¹ (F.j (z ^ i)⁻¹) hcen _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1 a
      have h5 := hTEig E n hodd.pos x U w₀ Up V w.1 w.2.1 hfree i hi t hT z hz B hB (F.tr.sec a)
      simp only [Pi.smul_apply]
      rw [h4, mul_smul, ← h5]
      congr 1
      refine finsum_congr fun y => ?_
      simp only [map_mul, hsz, hsl]
