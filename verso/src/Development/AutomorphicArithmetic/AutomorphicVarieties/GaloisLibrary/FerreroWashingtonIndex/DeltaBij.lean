import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ToZModPowOneEqZeroIff

open UpperTheory.V.FW

/- English proof (translation)
Take `⟨k, rfl⟩` from `ZMod.intCast_surjective x`. Rewrite using `[map_intCast, map_intCast, map_intCast]`. Both sides reduce to the same expression.
-/
private theorem crt_apply {a b : ℕ} (hab : a.Coprime b) (x : ZMod (a * b)) :
    ZMod.chineseRemainder hab x =
      (ZMod.castHom (Dvd.intro b rfl) (ZMod a) x, ZMod.castHom (Dvd.intro_left a rfl) (ZMod b) x) := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast, map_intCast, map_intCast]
  rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Apply `(ZMod.chineseRemainder hab).injective` to reduce the goal to its premises. Rewrite using `[crt_apply, crt_apply]`. Conclude with `Prod.ext (congrArg Units.val h1) (congrArg Units.val h2)`.
-/
private theorem crt_inj {a b : ℕ} (hab : a.Coprime b) (ha : a ∣ a * b) (hb : b ∣ a * b) (x y : (ZMod (a * b))ˣ)
    (h1 : ZMod.unitsMap ha x = ZMod.unitsMap ha y) (h2 : ZMod.unitsMap hb x = ZMod.unitsMap hb y) : x = y := by
  apply Units.ext
  apply (ZMod.chineseRemainder hab).injective
  rw [crt_apply, crt_apply]
  exact Prod.ext (congrArg Units.val h1) (congrArg Units.val h2)

/- English proof (translation)
Set `x : (ZMod (a * b))ˣ` to `Units.map (ZMod.chineseRemainder hab).symm.toMonoidHom (MulEquiv.prodUnits.symm (u, v))`. Establish `hx : ZMod.chineseRemainder hab (x : ZMod (a * b)) = ((u : ZMod a), (v : ZMod b))` using `(ZMod.chineseRemainder hab).apply_symm_apply _`. Rewrite `hx` using `[crt_apply]`. Conclude with `⟨x, Units.ext (congrArg Prod.fst hx), Units.ext (congrArg Prod.snd hx)⟩`.
-/
private theorem crt_surj {a b : ℕ} (hab : a.Coprime b) (ha : a ∣ a * b) (hb : b ∣ a * b)
    (u : (ZMod a)ˣ) (v : (ZMod b)ˣ) :
    ∃ x : (ZMod (a * b))ˣ, ZMod.unitsMap ha x = u ∧ ZMod.unitsMap hb x = v := by
  let x : (ZMod (a * b))ˣ :=
    Units.map (ZMod.chineseRemainder hab).symm.toMonoidHom (MulEquiv.prodUnits.symm (u, v))
  have hx : ZMod.chineseRemainder hab (x : ZMod (a * b)) = ((u : ZMod a), (v : ZMod b)) :=
    (ZMod.chineseRemainder hab).apply_symm_apply _
  rw [crt_apply] at hx
  exact ⟨x, Units.ext (congrArg Prod.fst hx), Units.ext (congrArg Prod.snd hx)⟩

/- English proof (translation)
Rewrite using `[← ZMod.unitsMap_comp h1 h2]`. Both sides reduce to the same expression.
-/
private theorem map_map {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (x : (ZMod c)ˣ) :
    ZMod.unitsMap h1 (ZMod.unitsMap h2 x) = ZMod.unitsMap (h1.trans h2) x := by
  rw [← ZMod.unitsMap_comp h1 h2]
  rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Conclude with `RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n hmn) (w : ℤ_[l])`.
-/
private theorem map_redU (l : ℕ) [Fact l.Prime] {m n : ℕ} (hmn : m ≤ n) (h : l ^ m ∣ l ^ n) (w : ℤ_[l]ˣ) :
    ZMod.unitsMap h (redU l n w) = redU l m w := by
  apply Units.ext
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n hmn) (w : ℤ_[l])

/- English proof (translation)
Introduce `l _ f n h h' hf hn`. Establish `hen : l ^ ee l ∣ l ^ n` using `pow_dvd_pow l hn`. Establish `hfe : f ∣ f * l ^ ee l` using `Dvd.intro _ rfl`. Establish `hle : l ^ ee l ∣ f * l ^ ee l` using `Dvd.intro_left _ rfl`. Establish `hfn : f ∣ f * l ^ n` using `Dvd.intro _ rfl`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_one]`. Introduce and unpack `⟨g, w, hw, hwg⟩ hg`. Establish `hg' : ZMod.unitsMap h g = 1` using `hg`. Establish `h1 : redU l (ee l) w = 1`.

Rewrite using `[← map_redU l hn hen, hwg, map_map, ← map_map hle h, hg', map_one]`. Establish `h2 : (⟨w, hw⟩ : WW l) = 1` using `(injective_iff_map_eq_one _).1 (teich l).1 _ h1`. Establish `h3 : w = 1` using `congrArg Subtype.val h2`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show g = 1`.

Apply `crt_inj (hf.pow_right n) hfn h'` to reduce the goal to its premises. Rewrite using `[← map_map hfe h, hg', map_one, map_one]`. Rewrite using `[← hwg, h3, map_one, map_one]`. Introduce `u`. Take `⟨w, hw⟩` from `(teich l).2 (ZMod.unitsMap hle u)`.

Establish `hw' : redU l (ee l) w = ZMod.unitsMap hle u` using `hw`. Take `⟨g, hg1, hg2⟩` from `crt_surj (hf.pow_right n) hfn h' (ZMod.unitsMap hfe u) (redU l n w)`. Use `⟨⟨g, w, w.2, hg2.symm⟩, ?_⟩` and prove the remaining obligations. Use `show ZMod.unitsMap h g = u`. Apply `crt_inj (hf.pow_right (ee l)) hfe hle` to reduce the goal to its premises.

Rewrite using `[map_map, hg1]`. Rewrite using `[map_map, ← map_map hen h', hg2, map_redU l hn, hw']`.
-/
theorem UpperTheory.V.FW.deltaBij :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ) (h : f * l ^ ee l ∣ f * l ^ n) (h' : l ^ n ∣ f * l ^ n), f.Coprime l → ee l ≤ n → Function.Bijective ((ZMod.unitsMap h).comp (((WW l).map (redU l n)).comap (ZMod.unitsMap h')).subtype) := by
  intro l _ f n h h' hf hn
  have hen : l ^ ee l ∣ l ^ n := pow_dvd_pow l hn
  have hfe : f ∣ f * l ^ ee l := Dvd.intro _ rfl
  have hle : l ^ ee l ∣ f * l ^ ee l := Dvd.intro_left _ rfl
  have hfn : f ∣ f * l ^ n := Dvd.intro _ rfl
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨g, w, hw, hwg⟩ hg
    have hg' : ZMod.unitsMap h g = 1 := hg
    have h1 : redU l (ee l) w = 1 := by
      rw [← map_redU l hn hen, hwg, map_map, ← map_map hle h, hg', map_one]
    have h2 : (⟨w, hw⟩ : WW l) = 1 := (injective_iff_map_eq_one _).1 (teich l).1 _ h1
    have h3 : w = 1 := congrArg Subtype.val h2
    apply Subtype.ext
    show g = 1
    apply crt_inj (hf.pow_right n) hfn h'
    · rw [← map_map hfe h, hg', map_one, map_one]
    · rw [← hwg, h3, map_one, map_one]
  · intro u
    obtain ⟨w, hw⟩ := (teich l).2 (ZMod.unitsMap hle u)
    have hw' : redU l (ee l) w = ZMod.unitsMap hle u := hw
    obtain ⟨g, hg1, hg2⟩ := crt_surj (hf.pow_right n) hfn h' (ZMod.unitsMap hfe u) (redU l n w)
    refine ⟨⟨g, w, w.2, hg2.symm⟩, ?_⟩
    show ZMod.unitsMap h g = u
    apply crt_inj (hf.pow_right (ee l)) hfe hle
    · rw [map_map, hg1]
    · rw [map_map, ← map_map hen h', hg2, map_redU l hn, hw']
