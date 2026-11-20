import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LamProdMonomial
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.RestCountOf
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FiniteRestrictSupport

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def lamG : Fin X.F.J → ℤ × Fin (r + K) → Fin n' × Fin (r + K) := fun _ v => (posOf n' v.1, v.2)

def lamE : Fin X.F.J → ℤ × Fin (r + K) → ℕ := fun j v => p ^ (X.F.dist (j.val : ℤ) v.1 + X.Rj p K (j.val : ℤ))

omit [NeZero n'] in

def lamL (la : Fin n' → Fin (r + K) → ℕ) : Fin n' × Fin (r + K) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => la v.1 v.2

def lamS (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) :
    Set (ℤ × Fin (r + K) →₀ ℕ) :=
  {m | (∀ v, m v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) ∧
    m ∈ segDegSet (r := r) K (X.bfam p K la e (j.val : ℤ)) ∧ m ∈ X.resSet p K (j.val : ℤ)}

end Dat

def RestLamA : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → ∀ (j : ℤ) (b : ℤ → ℕ),
    (∀ x, x ∉ X.F.letters j → b x = 0) →
    ∃ y : Fin (Module.finrank O (X.Mj p K O j b)) → SegRing O r K, (∀ i, y i ∈ X.Mj p K O j b) ∧
      LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (y i)

def RestLamInj (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ la ∈ X.LA p K, ∀ e ∈ X.EE p K la, ∀ la' ∈ X.LA p K, ∀ e' ∈ X.EE p K la',
    ∀ m m' : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j, m j ∈ X.lamS p K la e j) → (∀ j, m' j ∈ X.lamS p K la' e' j) →
      Dat.lamL K la + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j) =
        Dat.lamL K la' + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m' j) → (la = la' ∧ e = e') ∧ m = m'

def RestLamDeg (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ la ∈ X.LA p K, ∀ e ∈ X.EE p K la, X.IsCLabel p K (Dat.lamL K la) ∧
    ∀ m : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j, m j ∈ X.lamS p K la e j) →
      ∀ t, ∑ c : Fin (r + K), (Dat.lamL K la + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j)) (t, c) = X.a' p K t

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp [Dat.phc, lam_ph]`. Consider the case `add u v hu hv => simp only [map_add, hu, hv]`. Consider the case `mul_X q v h`. Simplify using `only [map_mul, h, map_X]`.

Simplify using `[Dat.phc, lam_ph, Dat.lamG, Dat.lamE]`.
-/
theorem lam_map_phc {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n' r : ℕ} [NeZero n'] (X : Dat n' r)
    (p K : ℕ) (j : Fin X.F.J) (P : SegRing R r K) :
    MvPolynomial.map f (X.phc p K R (j.val : ℤ) P) = lam_ph (X.lamG K) (X.lamE p K) j (MvPolynomial.map f P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Dat.phc, lam_ph]
  | add u v hu hv => simp only [map_add, hu, hv]
  | mul_X q v h =>
    simp only [map_mul, h, map_X]
    simp [Dat.phc, lam_ph, Dat.lamG, Dat.lamE]

/- English proof (translation)
Take `⟨⟨h1, h2⟩, h3⟩` from `hy`. Establish `hs` using `XX'_supported O X.F (j.val : ℤ) _ _ _ h1`. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`. Establish `hm' : m ∈ y.support` using `Finset.mem_coe.mp hm`.

Use `⟨fun v hv => ?_, (MvPolynomial.mem_restrictSupport_iff (R := O)).mp h2 hm, (MvPolynomial.mem_restrictSupport_iff (R := O)).mp h3 hm⟩` and prove the remaining obligations. Establish `hvars : v ∈ y.vars`. Rewrite using `[MvPolynomial.mem_vars_iff_mem_support]`. Conclude with `⟨m, hm', Finsupp.mem_support_iff.mpr hv⟩`. Conclude with `(MvPolynomial.mem_supported.mp hs) (Finset.mem_coe.mpr hvars)`.
-/
theorem lam_mem_lamS {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ) [NeZero K] (O : Type) [CommRing O]
    (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) {y : SegRing O r K}
    (hy : y ∈ X.Mj p K O (j.val : ℤ) (X.bfam p K la e (j.val : ℤ))) : y ∈ restrictSupport O (X.lamS p K la e j) := by
  classical
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy
  have hs := XX'_supported O X.F (j.val : ℤ) _ _ _ h1
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' : m ∈ y.support := Finset.mem_coe.mp hm
  refine ⟨fun v hv => ?_, (MvPolynomial.mem_restrictSupport_iff (R := O)).mp h2 hm,
    (MvPolynomial.mem_restrictSupport_iff (R := O)).mp h3 hm⟩
  have hvars : v ∈ y.vars := by
    rw [MvPolynomial.mem_vars_iff_mem_support]
    exact ⟨m, hm', Finsupp.mem_support_iff.mpr hv⟩
  exact (MvPolynomial.mem_supported.mp hs) (Finset.mem_coe.mpr hvars)

/- English proof (translation)
Introduce `p n' r K _ _ _ X O _ _ _ Sd hX hLa hk`. Set `SS` to `(X.LA p K).sigma fun la => X.EE p K la`. Set `Φ` to `{x // x ∈ SS}`. Establish `hΦ : ∀ f : Φ, f.1.1 ∈ X.LA p K ∧ f.1.2 ∈ X.EE p K f.1.1` using `fun f => Finset.mem_sigma.mp f.2`. Set `nn : Φ → Fin X.F.J → ℕ` to `fun f j => Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K f.1.1 f.1.2 (j.val : ℤ)))`.

Establish `hex` using `fun (f : Φ) (j : Fin X.F.J) => hA p n' r K X O Sd hX (j.val : ℤ) (X.bfam p K f.1.1 f.1.2 (j.val : ℤ)) (fun x hx => by simp [Dat.bfam, hx])`. Use `choose y hyM hyL using hex`. Use `set res := MvPolynomial.map (σ := ℤ × Fin (r + K)) (IsLocalRing.residue O) with hres`. Establish `hli` using `lam_li_all (F := FF O) (X.lamG K) (X.lamE p K) (fun f : Φ => Dat.lamL K f.1.1) (fun f j => X.lamS p K f.1.1 f.1.2 j) (fun f j => Fin (nn f j)) (fun f j i => res (y f j i)) (fun f j => hyL f j) (fun f j i => map_mem_restrictSupport _ _ (lam_mem_lamS X p K O f.1.1 f.1.2 j (hyM f j …`. Introduce `f f' m m' hm hm' h`.

Take `⟨⟨h1, h2⟩, h3⟩` from `hI p n' r K X hX hLa hk f.1.1 (hΦ f).1 f.1.2 (hΦ f).2 f'.1.1 (hΦ f').1 f'.1.2 (hΦ f').2 m m' hm hm' h`. Use `⟨Subtype.ext ?_, h3⟩` and prove the remaining obligations. Take `⟨⟨la, e⟩, hf⟩` from `f`. Take `⟨⟨la', e'⟩, hf'⟩` from `f'`. Simplify using `only at h1 h2`.

Substitute `h1` using the available equality. Substitute `h2` using the available equality. Use the proof step `rfl)`. Establish `hmem : ∀ x : (Σ f : Φ, ∀ j, Fin (nn f j)), monomial (Dat.lamL K x.1.1.1) (1 : FF O) * ∏ j, lam_ph (X.lamG K) (X.lamE p K) j (res (y x.1 j (x.2 j))) ∈ X.LamBar p K O`. Introduce and unpack `⟨f, a⟩`.

Set `Yf : Fin X.F.J → SegRing O r K` to `fun i => y f i (a i)`. Set `y' : ℤ → SegRing O r K` to `fun j => if h : 0 ≤ j ∧ j.toNat < X.F.J then Yf ⟨j.toNat, h.2⟩ else 0`. Establish `hy'i : ∀ i : Fin X.F.J, y' (i.val : ℤ) = Yf i`. Introduce `i`. Establish `h : 0 ≤ (i.val : ℤ) ∧ ((i.val : ℤ)).toNat < X.F.J` using `⟨by positivity, by simpa using i.isLt⟩`.

Simplify using `only [y', dif_pos h]`. Conclude with `congrArg Yf (Fin.ext (by simp))`. Take `⟨hlab, hdeg⟩` from `hD p n' r K X hX hLa hk f.1.1 (hΦ f).1 f.1.2 (hΦ f).2`. Establish `hprod : (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y' j)) = ∏ j : Fin X.F.J, lam_ph (R` using `O) (X.lamG K) (X.lamE p K) j (Yf j) := by`. Rewrite using `[Finset.prod_range]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hy'i]`. Both sides reduce to the same expression. Use `Submodule.subset_span ⟨(∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y' j)) * monomial (Dat.lamL K f.1.1) 1, ⟨fun j => X.bfam p K f.1.1 f.1.2 j, y', Dat.lamL K f.1.1, ?_, hlab, rfl, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `j`.

Distinguish the cases in `h : 0 ≤ j ∧ j.toNat < X.F.J`. Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le h.1`. Establish `hk' : k < X.F.J` using `by simpa using h.2`. Use `hy'i ⟨k, hk'⟩` as an intermediate fact. Simplify using `only at this`.

Rewrite using `[this]`. Conclude with `hyM f ⟨k, hk'⟩ (a ⟨k, hk'⟩)`. Simplify using `only [y', dif_neg h]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[hprod, lam_expand]`.

Unfold `RRdeg`. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `n hn`. Establish `hn'` using `MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hn)`. Rewrite `hn'` using `[mul_comm, coeff_monomial_mul']`.

Use `split_ifs at hn' with hle`. Rewrite `hn'` using `[one_mul, coeff_sum]`. Take `⟨m, hm, hm0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hn'`. Rewrite `hm0` using `[coeff_monomial]`. Use `split_ifs at hm0 with heq`.

Establish `hn2 : n = Dat.lamL K f.1.1 + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j)`. Rewrite using `[heq]`. Conclude with `(add_tsub_cancel_of_le hle).symm`. Introduce `t`. Rewrite using `[hn2]`.

Use `hdeg m (fun j => ?_) t` and prove the remaining obligations. Conclude with `(MvPolynomial.mem_restrictSupport_iff (R := O)).mp (lam_mem_lamS X p K O f.1.1 f.1.2 j (hyM f j (a j))) (Finset.mem_coe.mpr (Fintype.mem_piFinset.mp hm j))`. Conclude with `absurd rfl hm0`. Conclude with `absurd rfl hn'`. Rewrite using `[map_mul, map_monomial, map_one, mul_comm, Finset.prod_range, map_prod]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[lam_map_phc, hy'i]`. Establish `hfin : Module.Finite (FF O) (X.LamBar p K O)`. Use `finite_restrictSupport (FF O) _ _ (degSet_finite n' (r + K) (X.a' p K))` as an intermediate fact.

Use `Submodule.finiteDimensional_of_le (S₂ := restrictSupport (FF O) {m : Fin n' × Fin (r + K) →₀ ℕ | ∀ t, ∑ c : Fin (r + K), m (t, c) = X.a' p K t}) ?_` and prove the remaining obligations. Unfold `Dat.LamBar`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Take `⟨_, _, _, -, -, -, h⟩` from `hg`.

Conclude with `map_mem_restrictSupport _ _ h`. Establish `hli' : LinearIndependent (FF O) (fun x : (Σ f : Φ, ∀ j, Fin (nn f j)) => (⟨_, hmem x⟩ : X.LamBar p K O))`. Use `LinearIndependent.of_comp (X.LamBar p K O).subtype ?_` and prove the remaining obligations. Conclude with `hli`. Establish `hcard` using `hli'.fintype_card_le_finrank`.

Use `le_trans (le_of_eq ?_) hcard` and prove the remaining obligations. Rewrite using `[Fintype.card_sigma]`. Simplify using `only [Fintype.card_pi, Fintype.card_fin]`. Rewrite using `[← Finset.sum_sigma (X.LA p K) (fun la => X.EE p K la) (fun x => ∏ j : Fin X.F.J, Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K x.1 x.2 (j.val : ℤ))))]`. Conclude with `(Finset.sum_coe_sort SS (fun x => ∏ j : Fin X.F.J, Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K x.1 x.2 (j.val : ℤ))))).symm`.
-/
theorem restLam_of_rests (C₀ : ℝ) (hA : RestLamA) (hI : RestLamInj C₀) (hD : RestLamDeg C₀) : RestLam C₀ := by
  intro p n' r K _ _ _ X O _ _ _ Sd hX hLa hk
  classical
  let SS := (X.LA p K).sigma fun la => X.EE p K la
  let Φ := {x // x ∈ SS}
  have hΦ : ∀ f : Φ, f.1.1 ∈ X.LA p K ∧ f.1.2 ∈ X.EE p K f.1.1 := fun f => Finset.mem_sigma.mp f.2
  let nn : Φ → Fin X.F.J → ℕ := fun f j =>
    Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K f.1.1 f.1.2 (j.val : ℤ)))
  have hex := fun (f : Φ) (j : Fin X.F.J) => hA p n' r K X O Sd hX (j.val : ℤ) (X.bfam p K f.1.1 f.1.2 (j.val : ℤ))
    (fun x hx => by simp [Dat.bfam, hx])
  choose y hyM hyL using hex
  set res := MvPolynomial.map (σ := ℤ × Fin (r + K)) (IsLocalRing.residue O) with hres
  have hli := lam_li_all (F := FF O) (X.lamG K) (X.lamE p K) (fun f : Φ => Dat.lamL K f.1.1)
    (fun f j => X.lamS p K f.1.1 f.1.2 j) (fun f j => Fin (nn f j)) (fun f j i => res (y f j i))
    (fun f j => hyL f j)
    (fun f j i => map_mem_restrictSupport _ _ (lam_mem_lamS X p K O f.1.1 f.1.2 j (hyM f j i)))
    (by
      intro f f' m m' hm hm' h
      obtain ⟨⟨h1, h2⟩, h3⟩ := hI p n' r K X hX hLa hk f.1.1 (hΦ f).1 f.1.2 (hΦ f).2 f'.1.1 (hΦ f').1 f'.1.2 (hΦ f').2
        m m' hm hm' h
      refine ⟨Subtype.ext ?_, h3⟩
      obtain ⟨⟨la, e⟩, hf⟩ := f
      obtain ⟨⟨la', e'⟩, hf'⟩ := f'
      simp only at h1 h2
      subst h1
      subst h2
      rfl)

  have hmem : ∀ x : (Σ f : Φ, ∀ j, Fin (nn f j)),
      monomial (Dat.lamL K x.1.1.1) (1 : FF O) * ∏ j, lam_ph (X.lamG K) (X.lamE p K) j (res (y x.1 j (x.2 j))) ∈
        X.LamBar p K O := by
    rintro ⟨f, a⟩
    let Yf : Fin X.F.J → SegRing O r K := fun i => y f i (a i)
    let y' : ℤ → SegRing O r K := fun j => if h : 0 ≤ j ∧ j.toNat < X.F.J then Yf ⟨j.toNat, h.2⟩ else 0
    have hy'i : ∀ i : Fin X.F.J, y' (i.val : ℤ) = Yf i := by
      intro i
      have h : 0 ≤ (i.val : ℤ) ∧ ((i.val : ℤ)).toNat < X.F.J := ⟨by positivity, by simpa using i.isLt⟩
      simp only [y', dif_pos h]
      exact congrArg Yf (Fin.ext (by simp))
    obtain ⟨hlab, hdeg⟩ := hD p n' r K X hX hLa hk f.1.1 (hΦ f).1 f.1.2 (hΦ f).2
    have hprod : (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y' j)) =
        ∏ j : Fin X.F.J, lam_ph (R := O) (X.lamG K) (X.lamE p K) j (Yf j) := by
      rw [Finset.prod_range]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hy'i]
      rfl
    refine Submodule.subset_span ⟨(∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y' j)) *
      monomial (Dat.lamL K f.1.1) 1, ⟨fun j => X.bfam p K f.1.1 f.1.2 j, y', Dat.lamL K f.1.1, ?_, hlab, rfl, ?_⟩, ?_⟩
    · intro j
      by_cases h : 0 ≤ j ∧ j.toNat < X.F.J
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
        have hk' : k < X.F.J := by simpa using h.2
        have := hy'i ⟨k, hk'⟩
        simp only at this
        rw [this]
        exact hyM f ⟨k, hk'⟩ (a ⟨k, hk'⟩)
      · simp only [y', dif_neg h]
        exact Submodule.zero_mem _
    · rw [hprod, lam_expand]
      unfold RRdeg
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro n hn
      have hn' := MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hn)
      rw [mul_comm, coeff_monomial_mul'] at hn'
      split_ifs at hn' with hle
      · rw [one_mul, coeff_sum] at hn'
        obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
        rw [coeff_monomial] at hm0
        split_ifs at hm0 with heq
        · have hn2 : n = Dat.lamL K f.1.1 + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j) := by
            rw [heq]; exact (add_tsub_cancel_of_le hle).symm
          intro t
          rw [hn2]
          refine hdeg m (fun j => ?_) t
          exact (MvPolynomial.mem_restrictSupport_iff (R := O)).mp
            (lam_mem_lamS X p K O f.1.1 f.1.2 j (hyM f j (a j))) (Finset.mem_coe.mpr (Fintype.mem_piFinset.mp hm j))
        · exact absurd rfl hm0
      · exact absurd rfl hn'
    · rw [map_mul, map_monomial, map_one, mul_comm, Finset.prod_range, map_prod]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [lam_map_phc, hy'i]
  have hfin : Module.Finite (FF O) (X.LamBar p K O) := by
    have := finite_restrictSupport (FF O) _ _ (degSet_finite n' (r + K) (X.a' p K))
    refine Submodule.finiteDimensional_of_le
      (S₂ := restrictSupport (FF O) {m : Fin n' × Fin (r + K) →₀ ℕ | ∀ t, ∑ c : Fin (r + K), m (t, c) = X.a' p K t}) ?_
    unfold Dat.LamBar
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨_, _, _, -, -, -, h⟩ := hg
    exact map_mem_restrictSupport _ _ h
  have hli' : LinearIndependent (FF O) (fun x : (Σ f : Φ, ∀ j, Fin (nn f j)) =>
      (⟨_, hmem x⟩ : X.LamBar p K O)) := by
    refine LinearIndependent.of_comp (X.LamBar p K O).subtype ?_
    exact hli
  have hcard := hli'.fintype_card_le_finrank
  refine le_trans (le_of_eq ?_) hcard
  rw [Fintype.card_sigma]
  simp only [Fintype.card_pi, Fintype.card_fin]
  rw [← Finset.sum_sigma (X.LA p K) (fun la => X.EE p K la)
    (fun x => ∏ j : Fin X.F.J, Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K x.1 x.2 (j.val : ℤ))))]
  exact (Finset.sum_coe_sort SS
    (fun x => ∏ j : Fin X.F.J, Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K x.1 x.2 (j.val : ℤ))))).symm

end Formalism.MainNotions.SelectionLemmas.Pf
