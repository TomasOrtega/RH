import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelBaseChangeUniv
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLevelObjPullbackOfCharZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Establish `key : ∀ {a : G.GAf}, L.CongOne N a → L.CongOne 1 a`. Introduce `a ha v hv`. Take `⟨w, hw, e⟩` from `ha v hv`. Conclude with `⟨N • w, nsmul_mem hw N, by rw [e, one_smul]⟩`. Conclude with `⟨key hg.1, key hg.2⟩`.
-/
private theorem kn_le_one {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (N : ℕ) {g : G.GAf}
    (hg : g ∈ L.KN N) : g ∈ L.KN 1 := by
  have key : ∀ {a : G.GAf}, L.CongOne N a → L.CongOne 1 a := by
    intro a ha v hv
    obtain ⟨w, hw, e⟩ := ha v hv
    exact ⟨N • w, nsmul_mem hw N, by rw [e, one_smul]⟩
  exact ⟨key hg.1, key hg.2⟩

/- English proof (translation)
Introduce `hKN hComp hPull hOfMap hFree hPt hCart hEx`. Introduce `p _ D G L R _ _ gb X N' N hle u hu π Φ hW k _ _ x hx`. Establish `hu1 : u ∈ L.KN 1` using `kn_le_one L N hu`. Establish `hI1 : Integ L (1 : G.GAf)` using `UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _)`. Establish `hA1 : AdmK L (↑N') (↑N) (1 : G.GAf)`.

Introduce `v hv`. Simplify using `using hle hv`. Establish `hA0 : AdmK L (↑N') (↑N') (1 : G.GAf)` using `(hKN p D G L N').1 1 (one_mem _)`. Take `⟨π₁, Φ₁, hW1⟩` from `hEx p D G L R gb X N' N 1 hI1 hA1`. Establish `hpb1` using `hCart p D G L R gb _ _ (X N') (X N) 1 (one_mem _) π₁ Φ₁ hW1`.

Take `⟨_, o, ψ, φ, hψ, _⟩` from `hW`. Take `⟨ox, ⟨mx⟩⟩` from `UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ (X N').s) x rfl (X N').univ`. Take `⟨oo, ⟨m2⟩⟩` from `UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ (X N').s) x rfl o`. Take `⟨ψ', hψ', _⟩` from `hPull p D G L R gb _ _ _ _ x rfl _ _ (X N').univ o ox oo mx m2 ψ u hψ`. Establish `hn1 : Nonempty (GObjMap oo (X N').univ (𝟙 _ ≫ x))`.

Establish `h` using `Unique.gObjMap_comp m2 φ`. Establish `e : x ≫ π = 𝟙 _ ≫ x` using `by rw [hx, Category.id_comp]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Take `⟨mm⟩` from `hn1`. Take `⟨n⟩` from `BaseChange.gObjMap_cancel mm mx`.

Take `⟨θ, _, hθ⟩` from `hOfMap p D G L R gb _ _ N' oo ox n`. Establish `hα` using `hComp p D G L R gb _ _ _ N' N' ox oo ox ψ' θ u 1 hI1 hA0 hψ' hθ`. Rewrite `hα` using `[_root_.one_mul]`. Establish `hpt` using `(hPt p D G L R gb N' N' N (X N') (X N') (X N) 1 1 u u⁻¹ π₁ Φ₁ π₁ Φ₁ hW1 hW1 hI1 hI1 hA1 hA1 (inv_mem hu) (by rw [_root_.one_mul, inv_mul_cancel]) k (x ≫ (X N').s) x x rfl rfl ox ox mx mx (ψ' ≫ θ) hα).2`. Establish `hpb` using `IsPullback.paste_horiz mx.cart.1 hpb1`.

Establish `hid : ψ' ≫ θ = 𝟙 ox.A`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hpb.hom_ext` to reduce the goal to its premises. Simplify `hpt.symm` using `[Category.assoc]`. Simplify using the standard rewrite rules.

Rewrite `hα` using `[hid]`. Conclude with `hFree p D G L R gb k (x ≫ (X N').s) N' ox u hu1 hα`.
-/
theorem UpperTheory.Gal.G3.pWitFree :
    KNBasic → TransComp → TransPull → TransOfMap → TransFree → PtEq → WitCart → WitEx → WitFree := by
  intro hKN hComp hPull hOfMap hFree hPt hCart hEx
  intro p _ D G L R _ _ gb X N' N hle u hu π Φ hW k _ _ x hx
  have hu1 : u ∈ L.KN 1 := kn_le_one L N hu
  have hI1 : Integ L (1 : G.GAf) := UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _)
  have hA1 : AdmK L (↑N') (↑N) (1 : G.GAf) := by
    intro v hv
    simpa using hle hv
  have hA0 : AdmK L (↑N') (↑N') (1 : G.GAf) := (hKN p D G L N').1 1 (one_mem _)
  obtain ⟨π₁, Φ₁, hW1⟩ := hEx p D G L R gb X N' N 1 hI1 hA1
  have hpb1 := hCart p D G L R gb _ _ (X N') (X N) 1 (one_mem _) π₁ Φ₁ hW1
  obtain ⟨_, o, ψ, φ, hψ, _⟩ := hW
  obtain ⟨ox, ⟨mx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ (X N').s) x rfl (X N').univ
  obtain ⟨oo, ⟨m2⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ (X N').s) x rfl o
  obtain ⟨ψ', hψ', _⟩ := hPull p D G L R gb _ _ _ _ x rfl _ _ (X N').univ o ox oo mx m2 ψ u hψ
  have hn1 : Nonempty (GObjMap oo (X N').univ (𝟙 _ ≫ x)) := by
    have h := Unique.gObjMap_comp m2 φ
    have e : x ≫ π = 𝟙 _ ≫ x := by rw [hx, Category.id_comp]
    rwa [e] at h
  obtain ⟨mm⟩ := hn1
  obtain ⟨n⟩ := BaseChange.gObjMap_cancel mm mx
  obtain ⟨θ, _, hθ⟩ := hOfMap p D G L R gb _ _ N' oo ox n
  have hα := hComp p D G L R gb _ _ _ N' N' ox oo ox ψ' θ u 1 hI1 hA0 hψ' hθ
  rw [_root_.one_mul] at hα
  have hpt := (hPt p D G L R gb N' N' N (X N') (X N') (X N) 1 1 u u⁻¹ π₁ Φ₁ π₁ Φ₁ hW1 hW1 hI1 hI1
    hA1 hA1 (inv_mem hu) (by rw [_root_.one_mul, inv_mul_cancel]) k (x ≫ (X N').s) x x rfl rfl
    ox ox mx mx (ψ' ≫ θ) hα).2
  have hpb := IsPullback.paste_horiz mx.cart.1 hpb1
  have hid : ψ' ≫ θ = 𝟙 ox.A := by
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · simpa [Category.assoc] using hpt.symm
    · simp
  rw [hid] at hα
  exact hFree p D G L R gb k (x ≫ (X N').s) N' ox u hu1 hα
