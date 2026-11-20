import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.FundamentalDomainExists

noncomputable section

namespace PI.VolSemiDirect.W

open MeasureTheory

section Dec

variable {X : Type} [Group X] [TopologicalSpace X] {K N H : Subgroup X}

/- English proof (translation)
Use `he (e.symm k)` as an intermediate fact. Rewrite `this` using `[e.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem dec_coe (e : (N × H) ≃ₜ K) (he : ∀ p : N × H, ((e p : K) : X) = (p.1 : X) * (p.2 : X))
    (k : K) : (k : X) = ((e.symm k).1 : X) * ((e.symm k).2 : X) := by
  have := he (e.symm k)
  rwa [e.apply_symm_apply] at this

/- English proof (translation)
Establish `h1 : e (n1, h1) = e (n2, h2)` using `Subtype.ext (by rw [he, he]; exact h)`. Establish `h2` using `e.injective h1`. Conclude with `⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩`.
-/
theorem dec_unique (e : (N × H) ≃ₜ K) (he : ∀ p : N × H, ((e p : K) : X) = (p.1 : X) * (p.2 : X))
    {n1 n2 : N} {h1 h2 : H} (h : (n1 : X) * (h1 : X) = (n2 : X) * (h2 : X)) :
    n1 = n2 ∧ h1 = h2 := by
  have h1 : e (n1, h1) = e (n2, h2) := Subtype.ext (by rw [he, he]; exact h)
  have h2 := e.injective h1
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/- English proof (translation)
Rewrite using `[e.symm_apply_eq]`. Conclude with `Subtype.ext (by rw [he]; exact hk)`.
-/
theorem symm_eq (e : (N × H) ≃ₜ K) (he : ∀ p : N × H, ((e p : K) : X) = (p.1 : X) * (p.2 : X))
    {k : K} {n : N} {h : H} (hk : (k : X) = (n : X) * (h : X)) : e.symm k = (n, h) := by
  rw [e.symm_apply_eq]
  exact Subtype.ext (by rw [he]; exact hk)

end Dec

/- English proof (translation)
Use `Subgroup.mem_subgroupOf.mp γ.2` as an intermediate fact. Conclude with `(Subgroup.mem_inf.mp this).1`.
-/
theorem memΓ {X : Type} [Group X] {Γ K : Subgroup X} (γ : ratG Γ K) : ((γ : K) : X) ∈ Γ := by
  have := Subgroup.mem_subgroupOf.mp γ.2
  exact (Subgroup.mem_inf.mp this).1

def mkR {X : Type} [Group X] {Γ K : Subgroup X} (x : K) (hx : (x : X) ∈ Γ) : ratG Γ K :=
  ⟨x, Subgroup.mem_subgroupOf.2 ⟨hx, x.2⟩⟩

/- English proof (translation)
Introduce `X _ _ _ _ Γ K N H hS hR lK lN lH dK dN dH μK μN μH hK hN hH hP 𝓕 𝓕N 𝓕H h𝓕 h𝓕N h𝓕H`. Take `⟨hnorm, e, he⟩` from `hS`. Take `⟨_, _, _, _⟩` from `lK`. Take `⟨_, _, _, _⟩` from `lN`. Take `⟨_, _, _, _⟩` from `lH`.

Take `⟨_, _⟩` from `dK`. Take `⟨_, _⟩` from `dN`. Take `⟨_, _⟩` from `dH`. Establish `hNK : ∀ n : N, (n : X) ∈ K` using `fun n => by`. Establish `h` using `(e (n, 1)).2`.

Rewrite `h` using `[he]`. Simplify using `using h`. Establish `hHK : ∀ h : H, (h : X) ∈ K` using `fun h => by`. Establish `h'` using `(e (1, h)).2`. Rewrite `h'` using `[he]`.

Simplify using `using h'`. Take `⟨𝓕N0, mN0, uN0⟩` from `exists_sfd (ratG Γ N)`. Take `⟨𝓕H0, mH0, uH0⟩` from `exists_sfd (ratG Γ H)`. Establish `: MeasurableConstSMul (ratG Γ N) N` using `⟨fun γ => (continuous_const_mul ((γ : N))).measurable⟩`. Establish `: MeasurableConstSMul (ratG Γ H) H` using `⟨fun γ => (continuous_const_mul ((γ : H))).measurable⟩`.

Establish `: MeasurableConstSMul (ratG Γ K) K` using `⟨fun γ => (continuous_const_mul ((γ : K))).measurable⟩`. Establish `eN : μN 𝓕N = μN 𝓕N0` using `h𝓕N.measure_eq (IsFundamentalDomain.mk' mN0.nullMeasurableSet uN0)`. Establish `eH : μH 𝓕H = μH 𝓕H0` using `h𝓕H.measure_eq (IsFundamentalDomain.mk' mH0.nullMeasurableSet uH0)`. Set `𝓕0 : Set K` to `e.symm ⁻¹' (𝓕N0 ×ˢ 𝓕H0)`. Establish `hm0 : MeasurableSet 𝓕0` using `e.symm.continuous.measurable (mN0.prod mH0)`.

Establish `hkey : ∀ (k : K) (δ : ratG Γ K), k ∈ 𝓕0 → δ • k ∈ 𝓕0 → δ = 1`. Introduce `k δ hk hδk`. Use `set p := e.symm k with hp`. Use `set q := e.symm (δ : K) with hq`. Use `set r := e.symm (δ • k) with hr`.

Establish `hkX` using `dec_coe e he k`. Establish `hδX` using `dec_coe e he (δ : K)`. Establish `hrX` using `dec_coe e he (δ • k)`. Rewrite `hkX` using `[← hp]`. Rewrite `hδX` using `[← hq]`.

Rewrite `hrX` using `[← hr]`. Establish `hq2 : (q.2 : X) ∈ Γ` using `hR _ q.1.2 _ q.2.2 (hδX ▸ memΓ δ)`. Establish `hq1 : (q.1 : X) ∈ Γ`. Establish `: (q.1 : X) = ((δ : K) : X) * (q.2 : X)⁻¹` using `by rw [hδX]; group`. Rewrite using `[this]`.

Conclude with `Γ.mul_mem (memΓ δ) (Γ.inv_mem hq2)`. Establish `hcomb : ((δ • k : K) : X) = ((q.1 : X) * ((q.2 : X) * (p.1 : X) * (q.2 : X)⁻¹)) * ((q.2 : X) * (p.2 : X))` using `by show ((δ : K) : X) * (k : X) = _`. Rewrite using `[hδX, hkX]`. Use `group`. Set `n' : N` to `⟨(q.1 : X) * ((q.2 : X) * (p.1 : X) * (q.2 : X)⁻¹), N.mul_mem q.1.2 (hnorm _ q.2.2 _ p.1.2)⟩`.

Set `h' : H` to `⟨(q.2 : X) * (p.2 : X), H.mul_mem q.2.2 p.2.2⟩`. Take `⟨hr1, hr2⟩` from `dec_unique e he (n1 := r.1) (h1 := r.2) (n2 := n') (h2 := h') (by rw [← hrX, hcomb])`. Establish `hk' : p.1 ∈ 𝓕N0 ∧ p.2 ∈ 𝓕H0` using `hk`. Establish `hδk' : r.1 ∈ 𝓕N0 ∧ r.2 ∈ 𝓕H0` using `hδk`. Set `η : ratG Γ H` to `mkR q.2 hq2`.

Establish `hη : η • p.2 ∈ 𝓕H0`. Establish `: η • p.2 = r.2` using `by rw [hr2]; rfl`. Rewrite using `[this]`. Conclude with `hδk'.2`. Establish `hη1 : η = 1`.

Take `⟨γ0, -, hγ0⟩` from `uH0 p.2`. Establish `a` using `hγ0 η hη`. Establish `b` using `hγ0 1 (by show (1 : ratG Γ H) • p.2 ∈ 𝓕H0; rw [one_smul]; exact hk'.2)`. Rewrite using `[a, b]`. Establish `hq2' : (q.2 : X) = 1`.

Use `congrArg (fun t : ratG Γ H => ((t : H) : X)) hη1` as an intermediate fact. Simplify `this` using `[η, mkR]`. Set `ν : ratG Γ N` to `mkR q.1 hq1`. Establish `hν : ν • p.1 ∈ 𝓕N0`. Establish `: ν • p.1 = r.1`.

Rewrite using `[hr1]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (q.1 : X) * (p.1 : X) = (q.1 : X) * ((q.2 : X) * (p.1 : X) * (q.2 : X)⁻¹)`. Rewrite using `[hq2']`. Use `group`.

Rewrite using `[this]`. Conclude with `hδk'.1`. Establish `hν1 : ν = 1`. Take `⟨γ0, -, hγ0⟩` from `uN0 p.1`. Establish `a` using `hγ0 ν hν`.

Establish `b` using `hγ0 1 (by show (1 : ratG Γ N) • p.1 ∈ 𝓕N0; rw [one_smul]; exact hk'.1)`. Rewrite using `[a, b]`. Establish `hq1' : (q.1 : X) = 1`. Use `congrArg (fun t : ratG Γ N => ((t : N) : X)) hν1` as an intermediate fact. Simplify `this` using `[ν, mkR]`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((δ : K) : X) = 1`. Rewrite using `[hδX, hq1', hq2', one_mul]`. Establish `huniq : ∀ k : K, ∃! γ : ratG Γ K, γ • k ∈ 𝓕0`.

Introduce `k`. Use `set p := e.symm k with hp`. Establish `hkX` using `dec_coe e he k`. Rewrite `hkX` using `[← hp]`. Take `⟨η, hη, -⟩` from `uH0 p.2`.

Set `n' : N` to `⟨((η : H) : X) * (p.1 : X) * ((η : H) : X)⁻¹, hnorm _ (η : H).2 _ p.1.2⟩`. Take `⟨ν, hν, -⟩` from `uN0 n'`. Set `γK : K` to `⟨((ν : N) : X) * ((η : H) : X), K.mul_mem (hNK _) (hHK _)⟩`. Set `γ : ratG Γ K` to `mkR γK (Γ.mul_mem (memΓ ν) (memΓ η))`. Establish `hγk : γ • k ∈ 𝓕0` using `by show e.symm (γ • k) ∈ 𝓕N0 ×ˢ 𝓕H0`.

Rewrite using `[symm_eq e he (n := ν • n') (h := η • p.2)]`. Conclude with `⟨hν, hη⟩`. Use `show ((ν : N) : X) * ((η : H) : X) * (k : X) = ((ν : N) : X) * (((η : H) : X) * (p.1 : X) * ((η : H) : X)⁻¹) * (((η : H) : X) * (p.2 : X))`. Rewrite using `[hkX]`. Use `group`.

Use `⟨γ, hγk, fun γ' hγ' => ?_⟩` and prove the remaining obligations. Establish `h1 : (γ' * γ⁻¹) • (γ • k) ∈ 𝓕0` using `by rwa [smul_smul, inv_mul_cancel_right]`. Use `hkey _ _ hγk h1` as an intermediate fact. Conclude with `(mul_inv_eq_one.1 this)`. Establish `h𝓕0 : IsFundamentalDomain (ratG Γ K) 𝓕0 μK` using `IsFundamentalDomain.mk' hm0.nullMeasurableSet huniq`.

Establish `eK : μK 𝓕 = μK 𝓕0` using `h𝓕.measure_eq h𝓕0`. Establish `hm0'` using `hm0`. Take `⟨B, hBm, hBe⟩` from `hm0`. Establish `hPB` using `hP (B.indicator 1) (measurable_one.indicator hBm)`. Establish `hL : (fun k : K => B.indicator (1 : X → ENNReal) (k : X)) = 𝓕0.indicator 1`.

Use function extensionality and compare the values at `k`. Rewrite using `[← hBe]`. Both sides reduce to the same expression. Establish `hRfun : ∀ (m : N) (h : H), B.indicator (1 : X → ENNReal) ((m : X) * (h : X)) = 𝓕N0.indicator 1 m * 𝓕H0.indicator 1 h`. Introduce `m h`.

Establish `hmem : (m : X) * (h : X) ∈ B ↔ m ∈ 𝓕N0 ∧ h ∈ 𝓕H0`. Establish `h1 : (m : X) * (h : X) = ((e (m, h) : K) : X)` using `(he (m, h)).symm`. Establish `h2 : ((e (m, h) : K) : X) ∈ B ↔ e (m, h) ∈ 𝓕0`. Rewrite using `[← hBe]`. Both sides reduce to the same expression.

Rewrite using `[h1, h2]`. Use `show e.symm (e (m, h)) ∈ 𝓕N0 ×ˢ 𝓕H0 ↔ _`. Rewrite using `[e.symm_apply_apply]`. Both sides reduce to the same expression. Apply the tactic sequence `by_cases hm : m ∈ 𝓕N0 <;> by_cases hh : h ∈ 𝓕H0 <;>`.

Simplify using `[Set.indicator, hmem, hm, hh]`. Establish `hR2 : ∫⁻ m, ∫⁻ h, B.indicator (1 : X → ENNReal) ((m : X) * (h : X)) ∂μH ∂μN = μN 𝓕N0 * μH 𝓕H0`. Repeatedly rewrite using `[hRfun]`. Establish `hi : ∀ m : N, ∫⁻ h, 𝓕N0.indicator 1 m * 𝓕H0.indicator 1 h ∂μH = 𝓕N0.indicator 1 m * μH 𝓕H0`. Introduce `m`.

Rewrite using `[lintegral_const_mul _ (measurable_one.indicator mH0), lintegral_indicator_one mH0]`. Repeatedly rewrite using `[hi]`. Rewrite using `[lintegral_mul_const _ (measurable_one.indicator mN0), lintegral_indicator_one mN0]`. Establish `hL2 : ∫⁻ k, B.indicator (1 : X → ENNReal) (k : X) ∂μK = μK 𝓕0`. Rewrite using `[hL, lintegral_indicator_one hm0']`.

Rewrite using `[eK, eN, eH, ← hL2, ← hR2]`. Conclude with `hPB`.
-/
theorem volume_quotient_holds : VolG := by
  intro X _ _ _ _ Γ K N H hS hR lK lN lH dK dN dH μK μN μH hK hN hH hP 𝓕 𝓕N 𝓕H h𝓕 h𝓕N h𝓕H
  obtain ⟨hnorm, e, he⟩ := hS
  obtain ⟨_, _, _, _⟩ := lK
  obtain ⟨_, _, _, _⟩ := lN
  obtain ⟨_, _, _, _⟩ := lH
  obtain ⟨_, _⟩ := dK
  obtain ⟨_, _⟩ := dN
  obtain ⟨_, _⟩ := dH
  have hNK : ∀ n : N, (n : X) ∈ K := fun n => by
    have h := (e (n, 1)).2
    rw [he] at h
    simpa using h
  have hHK : ∀ h : H, (h : X) ∈ K := fun h => by
    have h' := (e (1, h)).2
    rw [he] at h'
    simpa using h'
  obtain ⟨𝓕N0, mN0, uN0⟩ := exists_sfd (ratG Γ N)
  obtain ⟨𝓕H0, mH0, uH0⟩ := exists_sfd (ratG Γ H)
  have : MeasurableConstSMul (ratG Γ N) N :=
    ⟨fun γ => (continuous_const_mul ((γ : N))).measurable⟩
  have : MeasurableConstSMul (ratG Γ H) H :=
    ⟨fun γ => (continuous_const_mul ((γ : H))).measurable⟩
  have : MeasurableConstSMul (ratG Γ K) K :=
    ⟨fun γ => (continuous_const_mul ((γ : K))).measurable⟩
  have eN : μN 𝓕N = μN 𝓕N0 := h𝓕N.measure_eq (IsFundamentalDomain.mk' mN0.nullMeasurableSet uN0)
  have eH : μH 𝓕H = μH 𝓕H0 := h𝓕H.measure_eq (IsFundamentalDomain.mk' mH0.nullMeasurableSet uH0)
  let 𝓕0 : Set K := e.symm ⁻¹' (𝓕N0 ×ˢ 𝓕H0)
  have hm0 : MeasurableSet 𝓕0 := e.symm.continuous.measurable (mN0.prod mH0)

  have hkey : ∀ (k : K) (δ : ratG Γ K), k ∈ 𝓕0 → δ • k ∈ 𝓕0 → δ = 1 := by
    intro k δ hk hδk
    set p := e.symm k with hp
    set q := e.symm (δ : K) with hq
    set r := e.symm (δ • k) with hr
    have hkX := dec_coe e he k
    have hδX := dec_coe e he (δ : K)
    have hrX := dec_coe e he (δ • k)
    rw [← hp] at hkX
    rw [← hq] at hδX
    rw [← hr] at hrX
    have hq2 : (q.2 : X) ∈ Γ := hR _ q.1.2 _ q.2.2 (hδX ▸ memΓ δ)
    have hq1 : (q.1 : X) ∈ Γ := by
      have : (q.1 : X) = ((δ : K) : X) * (q.2 : X)⁻¹ := by rw [hδX]; group
      rw [this]
      exact Γ.mul_mem (memΓ δ) (Γ.inv_mem hq2)
    have hcomb : ((δ • k : K) : X) =
        ((q.1 : X) * ((q.2 : X) * (p.1 : X) * (q.2 : X)⁻¹)) * ((q.2 : X) * (p.2 : X)) := by
      show ((δ : K) : X) * (k : X) = _
      rw [hδX, hkX]; group
    let n' : N := ⟨(q.1 : X) * ((q.2 : X) * (p.1 : X) * (q.2 : X)⁻¹),
      N.mul_mem q.1.2 (hnorm _ q.2.2 _ p.1.2)⟩
    let h' : H := ⟨(q.2 : X) * (p.2 : X), H.mul_mem q.2.2 p.2.2⟩
    obtain ⟨hr1, hr2⟩ := dec_unique e he (n1 := r.1) (h1 := r.2) (n2 := n') (h2 := h')
      (by rw [← hrX, hcomb])
    have hk' : p.1 ∈ 𝓕N0 ∧ p.2 ∈ 𝓕H0 := hk
    have hδk' : r.1 ∈ 𝓕N0 ∧ r.2 ∈ 𝓕H0 := hδk

    let η : ratG Γ H := mkR q.2 hq2
    have hη : η • p.2 ∈ 𝓕H0 := by
      have : η • p.2 = r.2 := by rw [hr2]; rfl
      rw [this]; exact hδk'.2
    have hη1 : η = 1 := by
      obtain ⟨γ0, -, hγ0⟩ := uH0 p.2
      have a := hγ0 η hη
      have b := hγ0 1 (by show (1 : ratG Γ H) • p.2 ∈ 𝓕H0; rw [one_smul]; exact hk'.2)
      rw [a, b]
    have hq2' : (q.2 : X) = 1 := by
      have := congrArg (fun t : ratG Γ H => ((t : H) : X)) hη1
      simpa [η, mkR] using this

    let ν : ratG Γ N := mkR q.1 hq1
    have hν : ν • p.1 ∈ 𝓕N0 := by
      have : ν • p.1 = r.1 := by
        rw [hr1]; apply Subtype.ext
        show (q.1 : X) * (p.1 : X) = (q.1 : X) * ((q.2 : X) * (p.1 : X) * (q.2 : X)⁻¹)
        rw [hq2']; group
      rw [this]; exact hδk'.1
    have hν1 : ν = 1 := by
      obtain ⟨γ0, -, hγ0⟩ := uN0 p.1
      have a := hγ0 ν hν
      have b := hγ0 1 (by show (1 : ratG Γ N) • p.1 ∈ 𝓕N0; rw [one_smul]; exact hk'.1)
      rw [a, b]
    have hq1' : (q.1 : X) = 1 := by
      have := congrArg (fun t : ratG Γ N => ((t : N) : X)) hν1
      simpa [ν, mkR] using this
    apply Subtype.ext; apply Subtype.ext
    show ((δ : K) : X) = 1
    rw [hδX, hq1', hq2', one_mul]

  have huniq : ∀ k : K, ∃! γ : ratG Γ K, γ • k ∈ 𝓕0 := by
    intro k
    set p := e.symm k with hp
    have hkX := dec_coe e he k
    rw [← hp] at hkX
    obtain ⟨η, hη, -⟩ := uH0 p.2
    let n' : N := ⟨((η : H) : X) * (p.1 : X) * ((η : H) : X)⁻¹, hnorm _ (η : H).2 _ p.1.2⟩
    obtain ⟨ν, hν, -⟩ := uN0 n'
    let γK : K := ⟨((ν : N) : X) * ((η : H) : X), K.mul_mem (hNK _) (hHK _)⟩
    let γ : ratG Γ K := mkR γK (Γ.mul_mem (memΓ ν) (memΓ η))
    have hγk : γ • k ∈ 𝓕0 := by
      show e.symm (γ • k) ∈ 𝓕N0 ×ˢ 𝓕H0
      rw [symm_eq e he (n := ν • n') (h := η • p.2)]
      · exact ⟨hν, hη⟩
      · show ((ν : N) : X) * ((η : H) : X) * (k : X) =
          ((ν : N) : X) * (((η : H) : X) * (p.1 : X) * ((η : H) : X)⁻¹) * (((η : H) : X) * (p.2 : X))
        rw [hkX]; group
    refine ⟨γ, hγk, fun γ' hγ' => ?_⟩
    have h1 : (γ' * γ⁻¹) • (γ • k) ∈ 𝓕0 := by rwa [smul_smul, inv_mul_cancel_right]
    have := hkey _ _ hγk h1
    exact (mul_inv_eq_one.1 this)
  have h𝓕0 : IsFundamentalDomain (ratG Γ K) 𝓕0 μK :=
    IsFundamentalDomain.mk' hm0.nullMeasurableSet huniq
  have eK : μK 𝓕 = μK 𝓕0 := h𝓕.measure_eq h𝓕0

  have hm0' := hm0
  obtain ⟨B, hBm, hBe⟩ := hm0
  have hPB := hP (B.indicator 1) (measurable_one.indicator hBm)
  have hL : (fun k : K => B.indicator (1 : X → ENNReal) (k : X)) = 𝓕0.indicator 1 := by
    funext k
    rw [← hBe]
    rfl
  have hRfun : ∀ (m : N) (h : H), B.indicator (1 : X → ENNReal) ((m : X) * (h : X)) =
      𝓕N0.indicator 1 m * 𝓕H0.indicator 1 h := by
    intro m h
    have hmem : (m : X) * (h : X) ∈ B ↔ m ∈ 𝓕N0 ∧ h ∈ 𝓕H0 := by
      have h1 : (m : X) * (h : X) = ((e (m, h) : K) : X) := (he (m, h)).symm
      have h2 : ((e (m, h) : K) : X) ∈ B ↔ e (m, h) ∈ 𝓕0 := by
        rw [← hBe]; rfl
      rw [h1, h2]
      show e.symm (e (m, h)) ∈ 𝓕N0 ×ˢ 𝓕H0 ↔ _
      rw [e.symm_apply_apply]
      rfl
    by_cases hm : m ∈ 𝓕N0 <;> by_cases hh : h ∈ 𝓕H0 <;>
      simp [Set.indicator, hmem, hm, hh]
  have hR2 : ∫⁻ m, ∫⁻ h, B.indicator (1 : X → ENNReal) ((m : X) * (h : X)) ∂μH ∂μN =
      μN 𝓕N0 * μH 𝓕H0 := by
    simp_rw [hRfun]
    have hi : ∀ m : N, ∫⁻ h, 𝓕N0.indicator 1 m * 𝓕H0.indicator 1 h ∂μH =
        𝓕N0.indicator 1 m * μH 𝓕H0 := by
      intro m
      rw [lintegral_const_mul _ (measurable_one.indicator mH0), lintegral_indicator_one mH0]
    simp_rw [hi]
    rw [lintegral_mul_const _ (measurable_one.indicator mN0), lintegral_indicator_one mN0]
  have hL2 : ∫⁻ k, B.indicator (1 : X → ENNReal) (k : X) ∂μK = μK 𝓕0 := by
    rw [hL, lintegral_indicator_one hm0']
  rw [eK, eN, eH, ← hL2, ← hR2]
  exact hPB

end PI.VolSemiDirect.W
