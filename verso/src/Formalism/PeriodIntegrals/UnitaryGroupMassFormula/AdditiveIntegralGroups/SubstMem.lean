import Mathlib

noncomputable section

namespace PI.AddIntG.Wk

def SerS {K : Type*} [CommRing K] (S : Subring K) (σ : Type*) : Subring (MvPowerSeries σ K) :=
  (MvPowerSeries.map S.subtype).range

/- English proof (translation)
Rewrite using `[SerS, RingHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩ e`. Rewrite using `[MvPowerSeries.coeff_map]`. Conclude with `(MvPowerSeries.coeff e g).2`.

Introduce `h`. Use `⟨(fun e => ⟨MvPowerSeries.coeff e f, h e⟩ : MvPowerSeries σ S), ?_⟩` and prove the remaining obligations. Use extensionality with `e`. Both sides reduce to the same expression.
-/
theorem mem_SerS {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    f ∈ SerS S σ ↔ ∀ e, MvPowerSeries.coeff e f ∈ S := by
  rw [SerS, RingHom.mem_range]
  constructor
  · rintro ⟨g, rfl⟩ e
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e g).2
  · intro h
    refine ⟨(fun e => ⟨MvPowerSeries.coeff e f, h e⟩ : MvPowerSeries σ S), ?_⟩
    ext e
    rfl

/- English proof (translation)
The claim follows from `RingHom.mem_range.mp hf`.
-/
theorem SerS_eq_map {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} {f : MvPowerSeries σ K}
    (hf : f ∈ SerS S σ) : ∃ g : MvPowerSeries σ S, MvPowerSeries.map S.subtype g = f :=
  RingHom.mem_range.mp hf

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← h]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_lift {K : Type*} [CommRing K] (S : Subring K) {σ : Type*}
    (g : MvPowerSeries σ S) {c : S} (h : MvPowerSeries.constantCoeff (MvPowerSeries.map S.subtype g) = (c : K)) :
    MvPowerSeries.constantCoeff g = c := by
  apply Subtype.ext
  rw [← h]
  simp

/- English proof (translation)
Take `⟨g, rfl⟩` from `SerS_eq_map S hf`. Establish `hg : MvPowerSeries.constantCoeff g = 1` using `constantCoeff_lift S g (c := 1) (by rw [h0]; rfl)`. Establish `h1 : g * MvPowerSeries.invOfUnit g 1 = 1` using `MvPowerSeries.mul_invOfUnit g 1 (by rw [hg]; rfl)`. Rewrite using `[SerS, RingHom.mem_range]`. Use `⟨MvPowerSeries.invOfUnit g 1, ?_⟩` and prove the remaining obligations.

Use `symm`. Rewrite using `[MvPowerSeries.inv_eq_iff_mul_eq_one (by rw [h0]; exact one_ne_zero), ← map_mul, mul_comm, h1, map_one]`.
-/
theorem inv_mem_SerS {K : Type*} [Field K] (S : Subring K) {σ : Type*} {f : MvPowerSeries σ K}
    (h0 : MvPowerSeries.constantCoeff f = 1) (hf : f ∈ SerS S σ) : f⁻¹ ∈ SerS S σ := by
  obtain ⟨g, rfl⟩ := SerS_eq_map S hf
  have hg : MvPowerSeries.constantCoeff g = 1 :=
    constantCoeff_lift S g (c := 1) (by rw [h0]; rfl)
  have h1 : g * MvPowerSeries.invOfUnit g 1 = 1 :=
    MvPowerSeries.mul_invOfUnit g 1 (by rw [hg]; rfl)
  rw [SerS, RingHom.mem_range]
  refine ⟨MvPowerSeries.invOfUnit g 1, ?_⟩
  symm
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one (by rw [h0]; exact one_ne_zero), ← map_mul, mul_comm, h1,
    map_one]

/- English proof (translation)
Rewrite `hf`, the goal using `[mem_SerS]`. Introduce `e`. Rewrite using `[MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)]`. Establish `hterm : ∀ d : σ →₀ ℕ, MvPowerSeries.coeff d f • MvPowerSeries.coeff e (d.prod fun s n => a s ^ n) ∈ S`. Introduce `d`.

Rewrite using `[smul_eq_mul]`. Use `S.mul_mem (hf d) ?_` and prove the remaining obligations. Establish `hp : (d.prod fun s n => a s ^ n) ∈ SerS S τ` using `Subring.prod_mem _ fun s _ => Subring.pow_mem _ (ha s) _`. Conclude with `(mem_SerS S _).1 hp e`. Rewrite using `[finsum_def]`.

Use `split_ifs`. Conclude with `Subring.sum_mem _ fun i _ => hterm _`. Conclude with `S.zero_mem`.
-/
theorem mvsubst_mem_SerS {K : Type*} [CommRing K] (S : Subring K) {σ τ : Type*} [Finite σ]
    {a : σ → MvPowerSeries τ K} {f : MvPowerSeries σ K} (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (ha : ∀ i, a i ∈ SerS S τ) (hf : f ∈ SerS S σ) : MvPowerSeries.subst a f ∈ SerS S τ := by
  classical
  rw [mem_SerS] at hf ⊢
  intro e
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)]
  have hterm : ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d f • MvPowerSeries.coeff e (d.prod fun s n => a s ^ n) ∈ S := by
    intro d
    rw [smul_eq_mul]
    refine S.mul_mem (hf d) ?_
    have hp : (d.prod fun s n => a s ^ n) ∈ SerS S τ :=
      Subring.prod_mem _ fun s _ => Subring.pow_mem _ (ha s) _
    exact (mem_SerS S _).1 hp e
  rw [finsum_def]
  split_ifs
  · exact Subring.sum_mem _ fun i _ => hterm _
  · exact S.zero_mem

/- English proof (translation)
The claim follows from `mvsubst_mem_SerS S (a := fun _ : Unit => a) (fun _ => ha0) (fun _ => ha) hf`.
-/
theorem subst_mem_SerS {K : Type*} [CommRing K] (S : Subring K) {τ : Type*} {a : MvPowerSeries τ K}
    {f : PowerSeries K} (ha0 : MvPowerSeries.constantCoeff a = 0) (ha : a ∈ SerS S τ)
    (hf : (f : MvPowerSeries Unit K) ∈ SerS S Unit) : PowerSeries.subst a f ∈ SerS S τ :=
  mvsubst_mem_SerS S (a := fun _ : Unit => a) (fun _ => ha0) (fun _ => ha) hf

end PI.AddIntG.Wk
