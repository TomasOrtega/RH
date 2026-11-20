import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.DeltaBij
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GamGen

open UpperTheory.V.FW

/- English proof (translation)
Apply the tactic sequence `unfold ee; split_ifs <;> omega`.
-/
private theorem ee_bd (l : ℕ) : 1 ≤ ee l ∧ ee l ≤ 2 := by
  unfold ee; split_ifs <;> omega

/- English proof (translation)
Establish `h2 : 2 < l ^ ee l`. Unfold `ee`. Use `split_ifs with h`. Substitute `h` using the available equality. Evaluate the numerical expressions.

Use `hl.out.two_le` as an intermediate fact. Rewrite using `[pow_one]`. Use linear arithmetic over natural numbers and integers. Unfold `WW`. Rewrite using `[mem_rootsOfUnity]`.

Conclude with `(Nat.totient_even h2).neg_one_pow`.
-/
private theorem neg_mem_WW (l : ℕ) [hl : Fact l.Prime] : (-1 : ℤ_[l]ˣ) ∈ WW l := by
  have h2 : 2 < l ^ ee l := by
    unfold ee
    split_ifs with h
    · subst h; norm_num
    · have := hl.out.two_le
      rw [pow_one]; omega
  unfold WW
  rw [mem_rootsOfUnity]
  exact (Nat.totient_even h2).neg_one_pow

/- English proof (translation)
Use `ext`. Simplify using `only [ZMod.unitsMap_def, redU, Units.coe_map, MonoidHom.coe_coe]`. Conclude with `RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n hmn) (w : ℤ_[l])`.
-/
private theorem red_red (l : ℕ) [Fact l.Prime] (m n : ℕ) (hmn : m ≤ n) (w : ℤ_[l]ˣ) :
    ZMod.unitsMap (pow_dvd_pow l hmn) (redU l n w) = redU l m w := by
  ext
  simp only [ZMod.unitsMap_def, redU, Units.coe_map, MonoidHom.coe_coe]
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n hmn) (w : ℤ_[l])

/- English proof (translation)
Introduce `l _ f n hf hn`. Establish `hl : l.Prime` using `Fact.out`. Establish `hee` using `ee_bd l`. Establish `hen : ee l ≤ n` using `by omega`. Establish `hf0 : f ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hf` using `[Nat.coprime_zero_left]`. Conclude with `hl.one_lt.ne' hf`. Establish `hdiv : f * l ^ ee l ∣ f * l ^ n` using `Nat.mul_dvd_mul_left f (pow_dvd_pow l hen)`. Establish `hdiv' : l ^ n ∣ f * l ^ n` using `Dvd.intro_left f rfl`.

Use `haveI : NeZero (f * l ^ n) := ⟨mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩`. Use `haveI : NeZero (f * l ^ ee l) := ⟨mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩`. Establish `hnil : IsNilpotent ((f : ZMod (f * l ^ n)) * (l : ZMod (f * l ^ n)) ^ ee l)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hz : ((f ^ n * l ^ (ee l * n) : ℕ) : ZMod (f * l ^ n)) = 0`.

Rewrite using `[ZMod.natCast_eq_zero_iff]`. Conclude with `Nat.mul_dvd_mul (dvd_pow_self f (by omega)) (pow_dvd_pow l (Nat.le_mul_of_pos_left n (by omega)))`. Rewrite using `[mul_pow, ← pow_mul]`. Conclude with `hz` after adjusting the coercions. Take `⟨γ, hγ⟩` from `hnil.isUnit_one_add`.

Take `⟨hker, hγpow⟩` from `gamGen l f n hdiv γ hf hen hγ`. Establish `hbij` using `deltaBij l f n hdiv hdiv' hf hen`. Set `e` to `MulEquiv.ofBijective _ hbij`. Set `σ : (ZMod (f * l ^ n))ˣ →* (ZMod (f * l ^ n))ˣ` to `(Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l))).subtype.comp (e.symm.toMonoidHom.comp (ZMod.unitsMap hdiv))`. Establish `hσπ : ∀ g, ZMod.unitsMap hdiv (σ g) = ZMod.unitsMap hdiv g` using `fun g => e.apply_symm_apply (ZMod.unitsMap hdiv g)`.

Establish `hσH : ∀ x ∈ Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l)), σ x = x`. Introduce `x hx`. Establish `h1 : ZMod.unitsMap hdiv x = e ⟨x, hx⟩` using `rfl`. Use `show ((e.symm (ZMod.unitsMap hdiv x) : _) : (ZMod (f * l ^ n))ˣ) = x`. Rewrite using `[h1, e.symm_apply_apply]`.

Establish `hcard : Nat.card (ZMod (f * l ^ ee l))ˣ = (f * l ^ ee l).totient`. Rewrite using `[Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]`. Establish `hσpow : ∀ g, σ g ^ (f * l ^ ee l).totient = 1`. Introduce `g`. Establish `h1 : (ZMod.unitsMap hdiv g) ^ (f * l ^ ee l).totient = 1`.

Rewrite using `[← hcard]`. Conclude with `pow_card_eq_one'`. Use `show ((e.symm (ZMod.unitsMap hdiv g) : _) : (ZMod (f * l ^ n))ˣ) ^ _ = 1`. Rewrite using `[← Subgroup.coe_pow, ← map_pow, h1, map_one, Subgroup.coe_one]`. Set `p : (ZMod (f * l ^ n))ˣ →* (ZMod (f * l ^ n))ˣ` to `MonoidHom.id _ / σ`.

Establish `hp : ∀ g, p g = g / σ g` using `fun g => rfl`. Establish `hQ : ∀ (n₀ : ℕ) (h : l ^ n₀ ∣ f * l ^ n), n₀ ≤ n → ∀ x ∈ Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l)), piQ l n₀ h x = 1`. Introduce `n₀ h hn₀ x hx`. Take `⟨w, hw, hwx⟩` from `Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx)`. Establish `hc` using `DFunLike.congr_fun (ZMod.unitsMap_comp (pow_dvd_pow l hn₀) hdiv') x`.

Simplify using `only [MonoidHom.comp_apply] at hc`. Use `show (QuotientGroup.mk' _) (ZMod.unitsMap h x) = 1`. Rewrite using `[QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← red_red l n₀ n hn₀ w, hwx]`.

Conclude with `hc`. Use `⟨γ, p, hγ, hγpow, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hsurj : Function.Surjective (ZMod.unitsMap hdiv)` using `fun y => by`. Take `⟨x, hx⟩` from `hbij.2 y`. Conclude with `⟨x.1, hx⟩`.

Rewrite using `[← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hcard]`. Introduce `g`. Rewrite using `[← hker, MonoidHom.mem_ker, hp, map_div, hσπ, div_self']`. Introduce `g`. Rewrite using `[hp, inv_div, mul_div_cancel]`.

Conclude with `hσpow g`. Establish `hm : (-1 : (ZMod (f * l ^ n))ˣ) ∈ Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l))`. Rewrite using `[Subgroup.mem_comap, Subgroup.mem_map]`. Use `⟨-1, neg_mem_WW l, ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using `[redU, ZMod.unitsMap_def]`. Rewrite using `[hp, hσH _ hm, div_self']`. Introduce `n₀ h hn₀`. Use `⟨fun g => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hp, map_div, hQ n₀ h hn₀ (σ g) (e.symm (ZMod.unitsMap hdiv g)).2, div_one]`.

Use `haveI : NeZero (l ^ n₀) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Establish `h1 : ZMod.unitsMap h γ ^ l ^ n = 1` using `by rw [← map_pow, hγpow, map_one]`. Establish `h2 : ZMod.unitsMap h γ ^ (l ^ n₀).totient = 1`. Rewrite using `[← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]`. Conclude with `pow_card_eq_one'`.

Take `⟨j, hj, hjx⟩` from `(Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one h1)`. Establish `hle : l ^ j ≤ l ^ n₀`. Rewrite using `[← hjx]`. Conclude with `(Nat.le_of_dvd (Nat.totient_pos.mpr (pow_pos hl.pos _)) (orderOf_dvd_of_pow_eq_one h2)).trans (Nat.totient_le _)`. Establish `hj0 : j ≤ n₀` using `(Nat.pow_le_pow_iff_right hl.one_lt).mp hle`.

Establish `hx : ZMod.unitsMap h γ ^ l ^ n₀ = 1`. Rewrite using `[← orderOf_dvd_iff_pow_eq_one, hjx]`. Conclude with `pow_dvd_pow l hj0`. Use `show (QuotientGroup.mk' _) (ZMod.unitsMap h γ) ^ l ^ n₀ = 1`. Rewrite using `[← map_pow, hx, map_one]`.
-/
theorem UpperTheory.V.FW.struct :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ), f.Coprime l → 2 ≤ n → ∃ (γ : (ZMod (f * l ^ n))ˣ) (p : (ZMod (f * l ^ n))ˣ →* (ZMod (f * l ^ n))ˣ), (γ : ZMod (f * l ^ n)) = 1 + f * l ^ ee l ∧ γ ^ l ^ n = 1 ∧ (Subgroup.zpowers γ).index = Nat.totient (f * l ^ ee l) ∧ (∀ g, p g ∈ Subgroup.zpowers γ) ∧ (∀ g, (g * (p g)⁻¹) ^ Nat.totient (f * l ^ ee l) = 1) ∧ p (-1) = 1 ∧ ∀ (n₀ : ℕ) (h : l ^ n₀ ∣ f * l ^ n), n₀ ≤ n → (∀ g, piQ l n₀ h (p g) = piQ l n₀ h g) ∧ piQ l n₀ h γ ^ l ^ n₀ = 1 := by
  intro l _ f n hf hn
  have hl : l.Prime := Fact.out
  have hee := ee_bd l
  have hen : ee l ≤ n := by omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hf
    exact hl.one_lt.ne' hf
  have hdiv : f * l ^ ee l ∣ f * l ^ n := Nat.mul_dvd_mul_left f (pow_dvd_pow l hen)
  have hdiv' : l ^ n ∣ f * l ^ n := Dvd.intro_left f rfl
  haveI : NeZero (f * l ^ n) := ⟨mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  haveI : NeZero (f * l ^ ee l) := ⟨mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  have hnil : IsNilpotent ((f : ZMod (f * l ^ n)) * (l : ZMod (f * l ^ n)) ^ ee l) := by
    refine ⟨n, ?_⟩
    have hz : ((f ^ n * l ^ (ee l * n) : ℕ) : ZMod (f * l ^ n)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.mul_dvd_mul (dvd_pow_self f (by omega))
        (pow_dvd_pow l (Nat.le_mul_of_pos_left n (by omega)))
    rw [mul_pow, ← pow_mul]
    exact_mod_cast hz
  obtain ⟨γ, hγ⟩ := hnil.isUnit_one_add
  obtain ⟨hker, hγpow⟩ := gamGen l f n hdiv γ hf hen hγ
  have hbij := deltaBij l f n hdiv hdiv' hf hen
  let e := MulEquiv.ofBijective _ hbij
  let σ : (ZMod (f * l ^ n))ˣ →* (ZMod (f * l ^ n))ˣ :=
    (Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l))).subtype.comp
      (e.symm.toMonoidHom.comp (ZMod.unitsMap hdiv))
  have hσπ : ∀ g, ZMod.unitsMap hdiv (σ g) = ZMod.unitsMap hdiv g := fun g =>
    e.apply_symm_apply (ZMod.unitsMap hdiv g)
  have hσH : ∀ x ∈ Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l)),
      σ x = x := by
    intro x hx
    have h1 : ZMod.unitsMap hdiv x = e ⟨x, hx⟩ := rfl
    show ((e.symm (ZMod.unitsMap hdiv x) : _) : (ZMod (f * l ^ n))ˣ) = x
    rw [h1, e.symm_apply_apply]
  have hcard : Nat.card (ZMod (f * l ^ ee l))ˣ = (f * l ^ ee l).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hσpow : ∀ g, σ g ^ (f * l ^ ee l).totient = 1 := by
    intro g
    have h1 : (ZMod.unitsMap hdiv g) ^ (f * l ^ ee l).totient = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    show ((e.symm (ZMod.unitsMap hdiv g) : _) : (ZMod (f * l ^ n))ˣ) ^ _ = 1
    rw [← Subgroup.coe_pow, ← map_pow, h1, map_one, Subgroup.coe_one]
  let p : (ZMod (f * l ^ n))ˣ →* (ZMod (f * l ^ n))ˣ := MonoidHom.id _ / σ
  have hp : ∀ g, p g = g / σ g := fun g => rfl
  have hQ : ∀ (n₀ : ℕ) (h : l ^ n₀ ∣ f * l ^ n), n₀ ≤ n →
      ∀ x ∈ Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l)),
      piQ l n₀ h x = 1 := by
    intro n₀ h hn₀ x hx
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx)
    have hc := DFunLike.congr_fun (ZMod.unitsMap_comp (pow_dvd_pow l hn₀) hdiv') x
    simp only [MonoidHom.comp_apply] at hc
    show (QuotientGroup.mk' _) (ZMod.unitsMap h x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨w, hw, ?_⟩
    rw [← red_red l n₀ n hn₀ w, hwx]
    exact hc
  refine ⟨γ, p, hγ, hγpow, ?_, ?_, ?_, ?_, ?_⟩
  · have hsurj : Function.Surjective (ZMod.unitsMap hdiv) := fun y => by
      obtain ⟨x, hx⟩ := hbij.2 y
      exact ⟨x.1, hx⟩
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hcard]
  · intro g
    rw [← hker, MonoidHom.mem_ker, hp, map_div, hσπ, div_self']
  · intro g
    rw [hp, inv_div, mul_div_cancel]
    exact hσpow g
  · have hm : (-1 : (ZMod (f * l ^ n))ˣ) ∈
        Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l)) := by
      rw [Subgroup.mem_comap, Subgroup.mem_map]
      refine ⟨-1, neg_mem_WW l, ?_⟩
      ext
      simp [redU, ZMod.unitsMap_def]
    rw [hp, hσH _ hm, div_self']
  · intro n₀ h hn₀
    refine ⟨fun g => ?_, ?_⟩
    · rw [hp, map_div, hQ n₀ h hn₀ (σ g) (e.symm (ZMod.unitsMap hdiv g)).2, div_one]
    · haveI : NeZero (l ^ n₀) := ⟨pow_ne_zero _ hl.ne_zero⟩
      have h1 : ZMod.unitsMap h γ ^ l ^ n = 1 := by rw [← map_pow, hγpow, map_one]
      have h2 : ZMod.unitsMap h γ ^ (l ^ n₀).totient = 1 := by
        rw [← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
        exact pow_card_eq_one'
      obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one h1)
      have hle : l ^ j ≤ l ^ n₀ := by
        rw [← hjx]
        exact (Nat.le_of_dvd (Nat.totient_pos.mpr (pow_pos hl.pos _))
          (orderOf_dvd_of_pow_eq_one h2)).trans (Nat.totient_le _)
      have hj0 : j ≤ n₀ := (Nat.pow_le_pow_iff_right hl.one_lt).mp hle
      have hx : ZMod.unitsMap h γ ^ l ^ n₀ = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hjx]
        exact pow_dvd_pow l hj0
      show (QuotientGroup.mk' _) (ZMod.unitsMap h γ) ^ l ^ n₀ = 1
      rw [← map_pow, hx, map_one]
