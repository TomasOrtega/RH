import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs

open UpperTheory.V.Af UpperTheory.V.Af.Gu
open GlobalTheory.DefiniteBC

/- English proof (translation)
Unfold `spehInf`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun k => Multiset.map (fun x => x + (((d:ℂ) - 1) / 2 - (k:ℂ))) m) d]`. Rewrite using `[Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]`.
-/
private theorem spehInf_eq_sum_shifted_map (d : ℕ) (m : Multiset ℂ) :
    spehInf d m = ∑ k : Fin d, Multiset.map (fun x => x + (((d:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) m := by
  unfold spehInf
  rw [Fin.sum_univ_eq_sum_range (fun k => Multiset.map (fun x => x + (((d:ℂ) - 1) / 2 - (k:ℂ))) m) d]
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]

/- English proof (translation)
Unfold `GlobalTheory.UnitaryBC.infOfWeight`. Use `Multiset.Nodup.map ?_ Finset.univ.nodup` and prove the remaining obligations. Introduce `a b h`. Establish `h2 : ((lam.w a - (a:ℕ) : ℤ) : ℂ) = ((lam.w b - (b:ℕ) : ℤ) : ℂ)`. Use `push_cast`.

Take the linear combination `h`. Establish `h3 : lam.w a - (a:ℕ) = lam.w b - (b:ℕ)` using `by exact_mod_cast h2`. Break down `lt_trichotomy a b with hab | hab | hab` into its components or cases. Use `lam.anti hab.le` as an intermediate fact. Establish `: (a:ℕ) < (b:ℕ)` using `hab`.

Use linear arithmetic over natural numbers and integers. Conclude with `hab`. Use `lam.anti hab.le` as an intermediate fact. Establish `: (b:ℕ) < (a:ℕ)` using `hab`. Use linear arithmetic over natural numbers and integers.
-/
private theorem infOfWeight_nodup' (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n) :
    (GlobalTheory.UnitaryBC.infOfWeight lam).Nodup := by
  unfold GlobalTheory.UnitaryBC.infOfWeight
  refine Multiset.Nodup.map ?_ Finset.univ.nodup
  intro a b h
  have h2 : ((lam.w a - (a:ℕ) : ℤ) : ℂ) = ((lam.w b - (b:ℕ) : ℤ) : ℂ) := by
    push_cast
    linear_combination h
  have h3 : lam.w a - (a:ℕ) = lam.w b - (b:ℕ) := by exact_mod_cast h2
  rcases lt_trichotomy a b with hab | hab | hab
  · have := lam.anti hab.le
    have : (a:ℕ) < (b:ℕ) := hab
    omega
  · exact hab
  · have := lam.anti hab.le
    have : (b:ℕ) < (a:ℕ) := hab
    omega

/- English proof (translation)
The claim follows from `map_sum (Multiset.mapAddMonoidHom g) f s`.
-/
private theorem multiset_map_finset_sum {ι : Type*} (s : Finset ι) (g : ℂ → ℂ) (f : ι → Multiset ℂ) :
    Multiset.map g (∑ i ∈ s, f i) = ∑ i ∈ s, Multiset.map g (f i) :=
  map_sum (Multiset.mapAddMonoidHom g) f s

/- English proof (translation)
Introduce `n c d m lam h`. Establish `hnd` using `infOfWeight_nodup' n lam`. Use `⟨fun i k => ?_, ?_⟩` and prove the remaining obligations. Establish `hle1 : Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i) ≤ spehInf (d i) (m i)`. Rewrite using `[spehInf_eq_sum_shifted_map]`.

Conclude with `Finset.single_le_sum (f := fun k : Fin (d i) => Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i)) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ k)`. Establish `hle2 : spehInf (d i) (m i) ≤ ∑ j, spehInf (d j) (m j)` using `Finset.single_le_sum (f := fun j => spehInf (d j) (m j)) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)`. Establish `hle : Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i) ≤ GlobalTheory.UnitaryBC.infOfWeight lam` using `h ▸ hle1.trans hle2`. Use `⟨(Multiset.nodup_of_le hle hnd).of_map _, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hmem` using `Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz)`.

Unfold `GlobalTheory.UnitaryBC.infOfWeight at hmem`. Rewrite `hmem` using `[Multiset.mem_map]`. Take `⟨j, -, hj⟩` from `hmem`. Use `⟨lam.w j - (j:ℕ), ?_⟩` and prove the remaining obligations. Unfold `ex`.

Use `push_cast`. Take the linear combination `(-1 : ℂ) * hj`. Rewrite using `[← h, multiset_map_finset_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[spehInf_eq_sum_shifted_map, multiset_map_finset_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Multiset.map_map]`. Use `Multiset.map_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Unfold `ex`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.speh_parameter_strings :
    Strings := by
  intro n c d m lam h
  have hnd := infOfWeight_nodup' n lam
  refine ⟨fun i k => ?_, ?_⟩
  · have hle1 : Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i) ≤ spehInf (d i) (m i) := by
      rw [spehInf_eq_sum_shifted_map]
      exact Finset.single_le_sum (f := fun k : Fin (d i) => Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i))
        (fun _ _ => Multiset.zero_le _) (Finset.mem_univ k)
    have hle2 : spehInf (d i) (m i) ≤ ∑ j, spehInf (d j) (m j) :=
      Finset.single_le_sum (f := fun j => spehInf (d j) (m j)) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
    have hle : Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i) ≤ GlobalTheory.UnitaryBC.infOfWeight lam :=
      h ▸ hle1.trans hle2
    refine ⟨(Multiset.nodup_of_le hle hnd).of_map _, fun z hz => ?_⟩
    have hmem := Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz)
    unfold GlobalTheory.UnitaryBC.infOfWeight at hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨j, -, hj⟩ := hmem
    refine ⟨lam.w j - (j:ℕ), ?_⟩
    unfold ex
    push_cast
    linear_combination (-1 : ℂ) * hj
  · rw [← h, multiset_map_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [spehInf_eq_sum_shifted_map, multiset_map_finset_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    unfold ex
    push_cast
    ring
