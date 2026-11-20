import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.NormChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentProperties

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V

namespace UpperTheory.V.Z.Inf

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0`. Simplify `w.ne_bot` using `[Ideal.absNorm_eq_zero_iff]`. Conclude with `h0` after adjusting the coercions.
-/
private theorem norm_ne (w : HeightOneSpectrum (𝓞 K)) : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  exact_mod_cast h0

/- English proof (translation)
Unfold `eulerL`. Use `tprod_congr fun w => ?_` and prove the remaining obligations. Rewrite using `[Multiset.map_map]`. Use `congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`.

Rewrite using `[mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]`. Use `congr 4`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem euler_shift (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (S : Set (HeightOneSpectrum (𝓞 K))) (z s : ℂ) :
    eulerL K (fun w => (B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) S (s - z) = eulerL K B S s := by
  unfold eulerL
  refine tprod_congr fun w => ?_
  rw [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]
  congr 4
  ring

/- English proof (translation)
Unfold `eulerLd eulerL`. Use `tprod_congr fun w => ?_` and prove the remaining obligations. Rewrite using `[Multiset.map_map, Multiset.map_map, Multiset.map_map]`. Use `congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`.

Rewrite using `[mul_inv, Complex.cpow_neg, inv_inv, mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]`. Use `congr 4`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem eulerd_shift (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (S : Set (HeightOneSpectrum (𝓞 K))) (z s : ℂ) :
    eulerLd K (fun w => (B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) S (s - z) = eulerLd K B S s := by
  unfold eulerLd eulerL
  refine tprod_congr fun w => ?_
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [mul_inv, Complex.cpow_neg, inv_inv, mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]
  congr 4
  ring

/- English proof (translation)
Rewrite using `[← Multiset.mapAddMonoidHom_apply, map_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `[Multiset.map_map, Function.comp_def]`.
-/
private theorem sum_shift {ι : Type} [Fintype ι] (m : ι → Multiset ℂ) (z : ℂ) :
    (∑ τ, (m τ).map (· + z)).map (· - z) = ∑ τ, m τ := by
  rw [← Multiset.mapAddMonoidHom_apply, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [Multiset.map_map, Function.comp_def]

end UpperTheory.V.Z.Inf

open UpperTheory.V.Z.Inf in
/- English proof (translation)
Introduce `hO hC K _ _ _ n hn σ m hm`. Set `x : GlobalTheory.ResW.Letter K` to `⟨n, σ⟩`. Establish `hd : ((n : ℂ) * (Module.finrank ℚ K : ℂ)) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')`. Set `z : ℂ` to `-GlobalTheory.ResW.cex x / ((n : ℂ) * (Module.finrank ℚ K : ℂ))`. Set `χ : HChar K` to `Model.absC K z`.

Establish `hspec` using `(GlobalTheory.ResW.letter_centralExponent K x).1`. Establish `htr : (Matrix.of (oneL K n)).trace = (n : ℝ) • (1 : Cinf K)`. Express the relevant statement in the definitionally equal form `(Matrix.of (fun i j : Fin n => if i = j then (1 : Cinf K) else 0)).trace = _`. Simplify using `[Matrix.trace, Nat.cast_smul_eq_nsmul]`. Establish `hz : ∀ φ ∈ (σ.twist χ).V, lie K n (oneL K n) φ = 0`.

Introduce and unpack `_ ⟨ψ, hψ, rfl⟩`. Establish `e0 : lie K n (oneL K n) ψ = GlobalTheory.ResW.cex x • ψ` using `hspec ψ hψ`. Establish `e1 : dchi χ (Matrix.of (oneL K n)).trace = -GlobalTheory.ResW.cex x`. Rewrite using `[htr, map_smul, GlobalTheory.ResW.dchi_absC_one_finrank]`. Establish `hzd : z * ((n : ℂ) * (Module.finrank ℚ K : ℂ)) = -GlobalTheory.ResW.cex x` using `div_mul_cancel₀ _ hd`.

Simplify using `only [Complex.real_smul, Complex.ofReal_natCast]`. Take the linear combination `hzd`. Express the relevant statement in the definitionally equal form `lie K n (oneL K n) (mulChi n χ ψ) = 0`. Rewrite using `[lie_mulChi, e0, e1, ← add_smul, add_neg_cancel, zero_smul, map_zero]`. Establish `hval : ∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)` using `fun v => by`.

Use `⟨fun y hy => Units.ext ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v y)) = 1`. Rewrite using `[GlobalTheory.Mem.Chr.CharModel.logNorm_local v y 0 (by simpa [IsUnitAt] using hy)]; simp`. Express the relevant statement in the definitionally equal form `Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v (atFin v (unif v)))) = _`. Establish `h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0` using `by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot`.

Rewrite using `[GlobalTheory.Mem.Chr.CharModel.logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0), ← Complex.natCast_log]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨S₀, hS⟩` from `hC K n hn (σ.twist χ) (Cm.carrier_le_central _ hz) (fun τ => (m τ).map (· + z)) (fun τ => by`.

Establish `h` using `(hm τ).twist χ`. Rewrite using `[show expo χ τ = z from Model.expo_absC z τ] at h)` and apply the resulting hypothesis. Use `⟨S₀, fun S hS₀ B hB => ?_⟩` and prove the remaining obligations. Establish `hP` using `hS S hS₀ (fun w => (B w).map (· * χ.val w)) fun w hw => by`. Establish `h` using `(hB w hw).twist (hval w).1`.

Rewrite `h` using `[CG.twist_mk]`. Then use the resulting hypothesis. Establish `hP2` using `hO.2 _ _ _ z hP`. Rewrite `hP2` using `[sum_shift]`. Establish `e : ∀ w, cx (fun w => (B w).map (· * χ.val w)) w = (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)` using `fun w => by`. Simplify using `only [cx, Multiset.map_map, Function.comp_def, Units.val_mul, (hval w).2]`.

Establish `e' : cx (fun w => (B w).map (· * χ.val w)) = fun w => (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)` using `funext e`. Rewrite `hP2` using `[e']`. Simplify `hP2` using `only [euler_shift, eulerd_shift]`.
-/
theorem UpperTheory.V.Z.Inf.sideOf :
    UpperTheory.V.Z.Inf.SideOf := by
  intro hO hC K _ _ _ n hn σ m hm
  let x : GlobalTheory.ResW.Letter K := ⟨n, σ⟩
  have hd : ((n : ℂ) * (Module.finrank ℚ K : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  let z : ℂ := -GlobalTheory.ResW.cex x / ((n : ℂ) * (Module.finrank ℚ K : ℂ))
  let χ : HChar K := Model.absC K z
  have hspec := (GlobalTheory.ResW.letter_centralExponent K x).1
  have htr : (Matrix.of (oneL K n)).trace = (n : ℝ) • (1 : Cinf K) := by
    change (Matrix.of (fun i j : Fin n => if i = j then (1 : Cinf K) else 0)).trace = _
    simp [Matrix.trace, Nat.cast_smul_eq_nsmul]
  have hz : ∀ φ ∈ (σ.twist χ).V, lie K n (oneL K n) φ = 0 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    have e0 : lie K n (oneL K n) ψ = GlobalTheory.ResW.cex x • ψ := hspec ψ hψ
    have e1 : dchi χ (Matrix.of (oneL K n)).trace = -GlobalTheory.ResW.cex x := by
      rw [htr, map_smul, GlobalTheory.ResW.dchi_absC_one_finrank]
      have hzd : z * ((n : ℂ) * (Module.finrank ℚ K : ℂ)) = -GlobalTheory.ResW.cex x := div_mul_cancel₀ _ hd
      simp only [Complex.real_smul, Complex.ofReal_natCast]
      linear_combination hzd
    change lie K n (oneL K n) (mulChi n χ ψ) = 0
    rw [lie_mulChi, e0, e1, ← add_smul, add_neg_cancel, zero_smul, map_zero]
  have hval : ∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z) := fun v => by
    refine ⟨fun y hy => Units.ext ?_, ?_⟩
    · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v y)) = 1
      rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v y 0 (by simpa [IsUnitAt] using hy)]; simp
    · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v (atFin v (unif v)))) = _
      have h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
      rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
        ← Complex.natCast_log]
      congr 1; push_cast; ring
  obtain ⟨S₀, hS⟩ := hC K n hn (σ.twist χ) (Cm.carrier_le_central _ hz) (fun τ => (m τ).map (· + z)) (fun τ => by
    have h := (hm τ).twist χ
    rwa [show expo χ τ = z from Model.expo_absC z τ] at h)
  refine ⟨S₀, fun S hS₀ B hB => ?_⟩
  have hP := hS S hS₀ (fun w => (B w).map (· * χ.val w)) fun w hw => by
    have h := (hB w hw).twist (hval w).1
    rwa [CG.twist_mk] at h
  have hP2 := hO.2 _ _ _ z hP
  rw [sum_shift] at hP2
  have e : ∀ w, cx (fun w => (B w).map (· * χ.val w)) w =
      (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z) := fun w => by
    simp only [cx, Multiset.map_map, Function.comp_def, Units.val_mul, (hval w).2]
  have e' : cx (fun w => (B w).map (· * χ.val w)) =
      fun w => (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z) := funext e
  rw [e'] at hP2
  simpa only [euler_shift, eulerd_shift] using hP2
