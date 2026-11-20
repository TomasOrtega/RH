import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMixedSymm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.SlabCover

open IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `hm' : (m : F) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Use `set g : Af F → Af F := fun x => algebraMap F (Af F) (m : F)⁻¹ * (x - y) with hg`. Establish `hgc : Continuous g` using `continuous_const.mul (continuous_id.sub continuous_const)`. Use `set U : Set (Af F) := g ⁻¹' {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F} with hU`. Establish `hUo : IsOpen U` using `(RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)).preimage hgc`.

Establish `hyU : y ∈ U`. Introduce `v`. Simplify using `only [hg, sub_self, mul_zero]`. Conclude with `zero_mem _`. Take `⟨ρ, hρ⟩` from `(PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 F) (K := F)).exists_mem_open hUo ⟨y, hyU⟩`.

Establish `hmm : (m : Af F) * algebraMap F (Af F) (m : F)⁻¹ = 1`. Rewrite using `[← map_natCast (algebraMap F (Af F)) m, ← map_mul, mul_inv_cancel₀ hm', map_one]`. Establish `he : algebraMap F (Af F) ρ = y + (m : Af F) * g (algebraMap F (Af F) ρ)`. Simplify using `only [hg, ← mul_assoc, hmm, one_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hint : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (algebraMap F (Af F) ρ) v ∈ v.adicCompletionIntegers F`. Introduce `v`. Rewrite using `[he]`. Use `show y v + (m : v.adicCompletion F) * (g (algebraMap F (Af F) ρ)) v ∈ v.adicCompletionIntegers F`. Conclude with `add_mem (hy v) (mul_mem (natCast_mem _ m) (hρ v))`.

Take `⟨r, hr⟩` from `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F ρ (fun v => by`. Establish `h` using `hint v`. Rewrite `h` using `[mem_adicCompletionIntegers]`. Conclude with `(valuedAdicCompletion_eq_valuation' v ρ).symm.trans_le h)`. Use `⟨r, -g (algebraMap F (Af F) ρ), fun v => ?_, ?_⟩` and prove the remaining obligations.

Use `show -(g (algebraMap F (Af F) ρ)) v ∈ v.adicCompletionIntegers F`. Conclude with `neg_mem (hρ v)`. Establish `: ((r : 𝓞 F) : F) = ρ` using `hr`. Rewrite using `[this]`. Use `conv_lhs => rw [he]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_int_approx (m : ℕ) (hm : 0 < m) (y : Af F)
    (hy : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, ∃ t : Af F, (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) ∧
      y - algebraMap F (Af F) (r : F) = (m : Af F) * t := by
  have hm' : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  set g : Af F → Af F := fun x => algebraMap F (Af F) (m : F)⁻¹ * (x - y) with hg
  have hgc : Continuous g := continuous_const.mul (continuous_id.sub continuous_const)
  set U : Set (Af F) := g ⁻¹' {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F} with hU
  have hUo : IsOpen U :=
    (RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)).preimage hgc
  have hyU : y ∈ U := by
    intro v
    simp only [hg, sub_self, mul_zero]
    exact zero_mem _
  obtain ⟨ρ, hρ⟩ := (PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 F) (K := F)).exists_mem_open hUo ⟨y, hyU⟩
  have hmm : (m : Af F) * algebraMap F (Af F) (m : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, mul_inv_cancel₀ hm', map_one]
  have he : algebraMap F (Af F) ρ = y + (m : Af F) * g (algebraMap F (Af F) ρ) := by
    simp only [hg, ← mul_assoc, hmm, one_mul]; ring
  have hint : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (algebraMap F (Af F) ρ) v ∈ v.adicCompletionIntegers F := by
    intro v
    rw [he]
    show y v + (m : v.adicCompletion F) * (g (algebraMap F (Af F) ρ)) v ∈ v.adicCompletionIntegers F
    exact add_mem (hy v) (mul_mem (natCast_mem _ m) (hρ v))
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F ρ
    (fun v => by
      have h := hint v
      rw [mem_adicCompletionIntegers] at h
      exact (valuedAdicCompletion_eq_valuation' v ρ).symm.trans_le h)
  refine ⟨r, -g (algebraMap F (Af F) ρ), fun v => ?_, ?_⟩
  · show -(g (algebraMap F (Af F) ρ)) v ∈ v.adicCompletionIntegers F
    exact neg_mem (hρ v)
  · have : ((r : 𝓞 F) : F) = ρ := hr
    rw [this]
    conv_lhs => rw [he]
    ring

/- English proof (translation)
Use `set b := RingOfIntegers.basis F`. Use `set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 F)`. Use `⟨(Fintype.piFinset fun _ : ι => Finset.range m).image (fun c => (((∑ k, (c k : ℤ) • b k : 𝓞 F)) : F)), ?_, ?_⟩` and prove the remaining obligations. Use `Finset.card_image_le.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ, ← Module.finrank_eq_card_basis b, RingOfIntegers.rank]`.

Introduce `r`. Establish `hmz : (0 : ℤ) < m` using `by exact_mod_cast hm`. Use `⟨_, Finset.mem_image.2 ⟨fun k => ((b.repr r k) % m).toNat, ?_, rfl⟩, ∑ k, ((b.repr r k) / m) • b k, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.mem_piFinset]`. Introduce `k`.

Rewrite using `[Finset.mem_range]`. Establish `h1` using `Int.emod_nonneg (b.repr r k) hmz.ne'`. Establish `h2` using `Int.emod_lt_of_pos (b.repr r k) hmz`. Use linear arithmetic over natural numbers and integers. Establish `hc : ∀ k, (((b.repr r k) % m).toNat : ℤ) = (b.repr r k) % m` using `fun k => Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))`.

Establish `key : r - ∑ k, (((b.repr r k) % m).toNat : ℤ) • b k = (m : 𝓞 F) * ∑ k, ((b.repr r k) / m) • b k`. Establish `hr` using `b.sum_repr r`. Use `set a := b.repr r`. Simplify using `only [hc, Finset.mul_sum]`. Use `conv_lhs => rw [← hr, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h` using `Int.emod_add_mul_ediv (a k) m`. Establish `h' : ((a k % m : ℤ) : 𝓞 F) + (m : 𝓞 F) * ((a k / m : ℤ) : 𝓞 F) = ((a k : ℤ) : 𝓞 F)`. Conclude with `congrArg (fun z : ℤ => (z : 𝓞 F)) h` after adjusting the coercions. Simplify using `only [zsmul_eq_mul]`.

Take the linear combination `(-(b k)) * h'`. Use `congrArg (fun x : 𝓞 F => (x : F)) key` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_residues (m : ℕ) (hm : 0 < m) :
    ∃ S : Finset F, S.card ≤ m ^ Module.finrank ℚ F ∧ ∀ r : 𝓞 F, ∃ ρ ∈ S, ∃ q : 𝓞 F, (r : F) - ρ = (m : F) * (q : F) := by
  set b := RingOfIntegers.basis F
  set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  refine ⟨(Fintype.piFinset fun _ : ι => Finset.range m).image
    (fun c => (((∑ k, (c k : ℤ) • b k : 𝓞 F)) : F)), ?_, ?_⟩
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ,
      ← Module.finrank_eq_card_basis b, RingOfIntegers.rank]
  · intro r
    have hmz : (0 : ℤ) < m := by exact_mod_cast hm
    refine ⟨_, Finset.mem_image.2 ⟨fun k => ((b.repr r k) % m).toNat, ?_, rfl⟩,
      ∑ k, ((b.repr r k) / m) • b k, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro k
      rw [Finset.mem_range]
      have h1 := Int.emod_nonneg (b.repr r k) hmz.ne'
      have h2 := Int.emod_lt_of_pos (b.repr r k) hmz
      omega
    · have hc : ∀ k, (((b.repr r k) % m).toNat : ℤ) = (b.repr r k) % m := fun k =>
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))
      have key : r - ∑ k, (((b.repr r k) % m).toNat : ℤ) • b k = (m : 𝓞 F) * ∑ k, ((b.repr r k) / m) • b k := by
        have hr := b.sum_repr r
        set a := b.repr r
        simp only [hc, Finset.mul_sum]
        conv_lhs => rw [← hr, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have h := Int.emod_add_mul_ediv (a k) m
        have h' : ((a k % m : ℤ) : 𝓞 F) + (m : 𝓞 F) * ((a k / m : ℤ) : 𝓞 F) = ((a k : ℤ) : 𝓞 F) := by
          exact_mod_cast congrArg (fun z : ℤ => (z : 𝓞 F)) h
        simp only [zsmul_eq_mul]
        linear_combination (-(b k)) * h'
      have := congrArg (fun x : 𝓞 F => (x : F)) key
      simpa using this

end GlobalTheory.ArchDecay.SlabCover

namespace GlobalTheory.ArchDecay.SlabCover

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `⟨S, hS, hres⟩` from `exists_residues (F := F) m hm`. Use `⟨S, hS, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨r, t, ht, hrt⟩` from `exists_int_approx m hm y hy`. Take `⟨ρ, hρS, q, hq⟩` from `hres r`. Use `⟨ρ, hρS, t + algebraMap F (Af F) (q : F), fun v => ?_, ?_⟩` and prove the remaining obligations.

Use `show t v + algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F q) ∈ v.adicCompletionIntegers F`. Conclude with `add_mem (ht v) (PI.UnipApproxD.IntegersDenseFiniteAdeles.int_R v q)`. Establish `e : algebraMap F (Af F) ρ = algebraMap F (Af F) (r : F) - (m : Af F) * algebraMap F (Af F) (q : F)`. Rewrite using `[← map_natCast (algebraMap F (Af F)) m, ← map_mul, ← map_sub, ← hq]`. Put the polynomial expressions in normal form.

Rewrite using `[e, mul_add, ← hrt]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_finite_residues (m : ℕ) (hm : 0 < m) :
    ∃ S : Finset F, S.card ≤ m ^ Module.finrank ℚ F ∧ ∀ y : Af F,
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F) →
      ∃ ρ ∈ S, ∃ z : Af F, (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), z v ∈ v.adicCompletionIntegers F) ∧
        y - algebraMap F (Af F) ρ = (m : Af F) * z := by
  obtain ⟨S, hS, hres⟩ := exists_residues (F := F) m hm
  refine ⟨S, hS, fun y hy => ?_⟩
  obtain ⟨r, t, ht, hrt⟩ := exists_int_approx m hm y hy
  obtain ⟨ρ, hρS, q, hq⟩ := hres r
  refine ⟨ρ, hρS, t + algebraMap F (Af F) (q : F), fun v => ?_, ?_⟩
  · show t v + algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F q) ∈ v.adicCompletionIntegers F
    exact add_mem (ht v) (PI.UnipApproxD.IntegersDenseFiniteAdeles.int_R v q)
  · have e : algebraMap F (Af F) ρ = algebraMap F (Af F) (r : F) - (m : Af F) * algebraMap F (Af F) (q : F) := by
      rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, ← map_sub, ← hq]; ring_nf
    rw [e, mul_add, ← hrt]; ring

end GlobalTheory.ArchDecay.SlabCover

namespace GlobalTheory.ArchDecay

open GlobalTheory.ArchDecay.SlabCover

/- English proof (translation)
Introduce `F _ _ κ _`. Use `⟨Module.finrank ℚ F * Fintype.card κ, fun m hm => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `w hw i`. Take `⟨a, ha0, hai, hae⟩` from `hw i`. Use `⟨(m : AF F) * a, ?_, fun v => ?_, ?_⟩` and prove the remaining obligations.

Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F ((m : Ainf F) * a.1) = 0`. Establish `: InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 = 0` using `ha0`. Rewrite using `[map_mul, this, mul_zero]`. Use `show ((m : AF F) * a).2 v ∈ v.adicCompletionIntegers F show (m : v.adicCompletion F) * a.2 v ∈ v.adicCompletionIntegers F`. Conclude with `mul_mem (natCast_mem _ m) (hai v)`.

Rewrite using `[hae, Nat.cast_one, one_mul]`. Take `⟨S, hS, hres⟩` from `exists_finite_residues (F := F) m hm`. Set `emb : (κ → F) → (κ → AF F)` to `fun f i => pairA F 0 (algebraMap F (Af F) (f i))`. Use `⟨(Fintype.piFinset fun _ : κ => S).image emb, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Finset.card_image_le.trans ?_` and prove the remaining obligations.

Rewrite using `[Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, pow_mul]`. Conclude with `Nat.pow_le_pow_left hS _`. Introduce `r hr`. Take `⟨f, -, rfl⟩` from `Finset.mem_image.1 hr`. Use function extensionality and compare the values at `i`.

Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0`. Conclude with `map_zero _`. Introduce `w hw`. Establish `hw'` using `hw`. Use `choose a ha0 hai hae using hw'`.

Establish `hy : ∀ i, ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (a i).2 v ∈ v.adicCompletionIntegers F` using `fun i v => hai i v`. Use `choose ρ hρS z hz hρz using fun i => hres (a i).2 (hy i)`. Use `⟨emb ρ, Finset.mem_image.2 ⟨ρ, Fintype.mem_piFinset.2 hρS, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `harch : arch F (emb ρ) = 0`. Use function extensionality and compare the values at `i`.

Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0`. Conclude with `map_zero _`. Establish `hout : archOut F κ (w - emb ρ) = archOut F κ w`. Rewrite using `[map_sub, archOut_apply F κ (emb ρ), harch, map_zero, sub_zero]`. Introduce `i`.

Use `⟨pairA F 0 (z i), map_zero _, fun v => hz i v, ?_⟩` and prove the remaining obligations. Establish `h1 : (a i).1 = 0`. Establish `: InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1 = 0` using `ha0 i`. Conclude with `(map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 this`. Establish `h2 : (w - archIn F κ (archOut F κ w)) i = a i` using `by rw [hae i, Nat.cast_one, one_mul]`.

Rewrite using `[hout]`. Establish `h3 : (w - emb ρ - archIn F κ (archOut F κ w)) i = (w - archIn F κ (archOut F κ w)) i - emb ρ i`. Simplify using `only [Pi.sub_apply]`. Normalize the expressions using the abelian group laws. Rewrite using `[h3, h2]`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (a i).1 - 0 = (m : Ainf F) * 0`. Rewrite using `[h1, sub_zero, mul_zero]`. Use `show (a i).2 - algebraMap F (Af F) (ρ i) = (m : Af F) * z i`. Conclude with `hρz i`.
-/
theorem slab_subset_and_cover : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c : ℕ, ∀ m : ℕ, 0 < m →
    slab F κ m ⊆ slab F κ 1 ∧ ∃ R : Finset (κ → AF F), R.card ≤ m ^ c ∧ (∀ r ∈ R, arch F r = 0) ∧
      ∀ w ∈ slab F κ 1, ∃ r ∈ R, w - r ∈ slab F κ m := by
  intro F _ _ κ _
  refine ⟨Module.finrank ℚ F * Fintype.card κ, fun m hm => ⟨?_, ?_⟩⟩
  · intro w hw i
    obtain ⟨a, ha0, hai, hae⟩ := hw i
    refine ⟨(m : AF F) * a, ?_, fun v => ?_, ?_⟩
    · show InfiniteAdeleRing.ringEquiv_mixedSpace F ((m : Ainf F) * a.1) = 0
      have : InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 = 0 := ha0
      rw [map_mul, this, mul_zero]
    · show ((m : AF F) * a).2 v ∈ v.adicCompletionIntegers F
      show (m : v.adicCompletion F) * a.2 v ∈ v.adicCompletionIntegers F
      exact mul_mem (natCast_mem _ m) (hai v)
    · rw [hae, Nat.cast_one, one_mul]
  · obtain ⟨S, hS, hres⟩ := exists_finite_residues (F := F) m hm
    let emb : (κ → F) → (κ → AF F) := fun f i => pairA F 0 (algebraMap F (Af F) (f i))
    refine ⟨(Fintype.piFinset fun _ : κ => S).image emb, ?_, ?_, ?_⟩
    · refine Finset.card_image_le.trans ?_
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, pow_mul]
      exact Nat.pow_le_pow_left hS _
    · intro r hr
      obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hr
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    · intro w hw
      have hw' := hw
      choose a ha0 hai hae using hw'
      have hy : ∀ i, ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (a i).2 v ∈ v.adicCompletionIntegers F :=
        fun i v => hai i v
      choose ρ hρS z hz hρz using fun i => hres (a i).2 (hy i)
      refine ⟨emb ρ, Finset.mem_image.2 ⟨ρ, Fintype.mem_piFinset.2 hρS, rfl⟩, ?_⟩
      have harch : arch F (emb ρ) = 0 := by
        funext i
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      have hout : archOut F κ (w - emb ρ) = archOut F κ w := by
        rw [map_sub, archOut_apply F κ (emb ρ), harch, map_zero, sub_zero]
      intro i
      refine ⟨pairA F 0 (z i), map_zero _, fun v => hz i v, ?_⟩
      have h1 : (a i).1 = 0 := by
        have : InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1 = 0 := ha0 i
        exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 this
      have h2 : (w - archIn F κ (archOut F κ w)) i = a i := by rw [hae i, Nat.cast_one, one_mul]
      rw [hout]
      have h3 : (w - emb ρ - archIn F κ (archOut F κ w)) i = (w - archIn F κ (archOut F κ w)) i - emb ρ i := by
        simp only [Pi.sub_apply]; abel
      rw [h3, h2]
      refine Prod.ext ?_ ?_
      · show (a i).1 - 0 = (m : Ainf F) * 0
        rw [h1, sub_zero, mul_zero]
      · show (a i).2 - algebraMap F (Af F) (ρ i) = (m : Af F) * z i
        exact hρz i

end GlobalTheory.ArchDecay
