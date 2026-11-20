import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsFiniteOfCompEtaleSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Introduce `hS hU hC hF p _ D G L R _ _ gb X N' N hA π Φ hW`. Set `M : Lv p` to `⟨N.1 * N'.1, Nat.le_trans N.2.1 (Nat.le_mul_of_pos_right _ (by have := N'.2.1; omega)), Nat.Coprime.mul_left N.2.2 N'.2.2⟩`. Establish `hI : Integ L (1 : G.GAf)` using `fun v hv => by simpa using hv`. Establish `hMN : AdmK L M.1 N.1 1` using `fun u hu => by`. Simplify using `using UpperTheory.Gal.Int.Geo.KN_anti (Dvd.intro _ rfl : N.1 ∣ M.1) hu`.

Take `⟨c, Φc, Wc, cF, cE, cS⟩` from `hF p D G L R gb N' M (Dvd.intro_left _ rfl) (X N') (X M)`. Take `⟨e, Φe, We, eF, eE, eS⟩` from `hF p D G L R gb N M (Dvd.intro _ rfl) (X N) (X M)`. Establish `W1` using `(hC p D G L R gb M N' N (X M) (X N') (X N) 1 1).2 hI hA c Φc π Φ Wc hW`. Rewrite `W1` using `[_root_.mul_one]`. Establish `hce : c ≫ π = e` using `(hU p D G L R gb M N (X M) (X N) 1 hI hMN _ _ _ _ W1 We).1`.

Take `⟨s1, s2, s3, -⟩` from `hS p D R gb N' (X N')`. Take `⟨t1, t2, t3, -⟩` from `hS p D R gb N (X N)`. Establish `hs : π ≫ (X N).s = (X N').s` using `hW.1`. Establish `sep : IsSeparated (π ≫ (X N).s)` using `by rw [hs]; exact s2`. Establish `lft : LocallyOfFiniteType (π ≫ (X N).s)` using `by rw [hs]; infer_instance`.

Establish `πS : IsSeparated π` using `IsSeparated.of_comp π (X N).s`. Establish `πL : LocallyOfFiniteType π` using `locallyOfFiniteType_of_comp π (X N).s`. Establish `hE : Etale (c ≫ π)` using `by rw [hce]; exact eE`. Establish `hFi : IsFinite (c ≫ π)` using `by rw [hce]; exact eF`. Take `⟨r1, r2⟩` from `GlobalTheory.etale_isFinite_of_comp_etale_surjective _ _ _ c π cE cS hE hFi πS πL`.

Establish `hSu : Surjective (c ≫ π)` using `by rw [hce]; exact eS`. Conclude with `⟨r2, r1, Surjective.of_comp c π⟩`.
-/
theorem UpperTheory.Gal.G3.pWitOne :
    GenSm → WitUniq → WitComp → WitForget → WitOne := by
  intro hS hU hC hF p _ D G L R _ _ gb X N' N hA π Φ hW
  let M : Lv p := ⟨N.1 * N'.1, Nat.le_trans N.2.1 (Nat.le_mul_of_pos_right _ (by have := N'.2.1; omega)),
    Nat.Coprime.mul_left N.2.2 N'.2.2⟩
  have hI : Integ L (1 : G.GAf) := fun v hv => by simpa using hv
  have hMN : AdmK L M.1 N.1 1 := fun u hu => by
    simpa using UpperTheory.Gal.Int.Geo.KN_anti (Dvd.intro _ rfl : N.1 ∣ M.1) hu
  obtain ⟨c, Φc, Wc, cF, cE, cS⟩ := hF p D G L R gb N' M (Dvd.intro_left _ rfl) (X N') (X M)
  obtain ⟨e, Φe, We, eF, eE, eS⟩ := hF p D G L R gb N M (Dvd.intro _ rfl) (X N) (X M)
  have W1 := (hC p D G L R gb M N' N (X M) (X N') (X N) 1 1).2 hI hA c Φc π Φ Wc hW
  rw [_root_.mul_one] at W1
  have hce : c ≫ π = e := (hU p D G L R gb M N (X M) (X N) 1 hI hMN _ _ _ _ W1 We).1
  obtain ⟨s1, s2, s3, -⟩ := hS p D R gb N' (X N')
  obtain ⟨t1, t2, t3, -⟩ := hS p D R gb N (X N)
  have hs : π ≫ (X N).s = (X N').s := hW.1
  have sep : IsSeparated (π ≫ (X N).s) := by rw [hs]; exact s2
  have lft : LocallyOfFiniteType (π ≫ (X N).s) := by rw [hs]; infer_instance
  have πS : IsSeparated π := IsSeparated.of_comp π (X N).s
  have πL : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π (X N).s
  have hE : Etale (c ≫ π) := by rw [hce]; exact eE
  have hFi : IsFinite (c ≫ π) := by rw [hce]; exact eF
  obtain ⟨r1, r2⟩ := GlobalTheory.etale_isFinite_of_comp_etale_surjective _ _ _ c π cE cS hE hFi πS πL
  have hSu : Surjective (c ≫ π) := by rw [hce]; exact eS
  exact ⟨r2, r1, Surjective.of_comp c π⟩
