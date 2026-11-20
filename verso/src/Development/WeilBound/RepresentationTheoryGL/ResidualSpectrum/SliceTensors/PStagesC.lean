import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStagesB

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.InductionInStages

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a d N : ℕ}

/- English proof (translation)
Take `⟨G, hG, rfl⟩` from `hF`. Introduce `u hu g`. Establish `h1 : chiDet N (Model.absC E z) u = 1`. Simplify using `only [chiDet, MonoidHom.comp_apply, det_eq_one_of_mem_unipRad (Ad E) hu, map_one]`. Express the relevant statement in the definitionally equal form `(mulChi N (Model.absC E z) G).1 (u * g) = (mulChi N (Model.absC E z) G).1 g`.

Rewrite using `[mulChi_apply, mulChi_apply, hG.1 u hu g, map_mul, h1, one_mul]`.
-/
theorem tw_unip_inv {h : ∑ _ : Fin d, a = N} {fam : Fin d → CuspSub E a} {z : ℂ} {F : Sm E N}
    (hF : F ∈ tw (indForms h fam) z) : ∀ u ∈ unipRad (Ad E) (stdBlocks (fun _ : Fin d => a) h), ∀ g, F.1 (u * g) = F.1 g := by
  obtain ⟨G, hG, rfl⟩ := hF
  intro u hu g
  have h1 : chiDet N (Model.absC E z) u = 1 := by
    simp only [chiDet, MonoidHom.comp_apply, det_eq_one_of_mem_unipRad (Ad E) hu, map_one]
  change (mulChi N (Model.absC E z) G).1 (u * g) = (mulChi N (Model.absC E z) G).1 g
  rw [mulChi_apply, mulChi_apply, hG.1 u hu g, map_mul, h1, one_mul]

/- English proof (translation)
Take `⟨G, hG, rfl⟩` from `hF`. Establish `h1` using `tensorForms_mulChi fam (Model.absC E z) (hG.2.2.2 1 1)`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `m`. Express the relevant statement in the definitionally equal form `(mulChi N (Model.absC E z) G).1 _ = _`.

Rewrite using `[mulChi_apply, chiDet_leviEmb]`. Simplify using the standard rewrite rules.
-/
theorem tw_slice_mem {h : ∑ _ : Fin d, a = N} {fam : Fin d → CuspSub E a} {z : ℂ} {F : Sm E N}
    (hF : F ∈ tw (indForms h fam) z) :
    (fun m : Fin d → GA E a => F.1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d => a) h) m)) ∈
      tensorForms (n := fun _ => a) (fun b => (fam b).twist (Model.absC E z)) := by
  obtain ⟨G, hG, rfl⟩ := hF
  have h1 := tensorForms_mulChi fam (Model.absC E z) (hG.2.2.2 1 1)
  convert h1 using 1
  funext m
  change (mulChi N (Model.absC E z) G).1 _ = _
  rw [mulChi_apply, chiDet_leviEmb]
  simp

variable {r s d₁ d₂ : ℕ}

/- English proof (translation)
Establish `key : ∀ w ∈ unipRad (Ad E) (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H), ∀ (m : Fin (d₁ + d₂) → GA E a) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)), Φ.1 (w * leviEmb (Ad E) (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) …`. Introduce `w hw m k g`. Take `⟨x, w₁, w₂, hw₁, hw₂, rfl⟩` from `unipRad_split h₁ h₂ H hw`. Take `⟨n, F₁, F₂, hF₁, hF₂, hΦ⟩` from `hsl k g`. Rewrite using `[leviEmb_split h₁ h₂ H, mul_assoc (unip x), ← map_mul, Prod.mk_mul_mk, mul_assoc, hu, hΦ, hΦ]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[tw_unip_inv (hF₁ i) w₁ hw₁, tw_unip_inv (hF₂ i) w₂ hw₂]`. Use `⟨fun u hu g' => ?_, hsm, hfv, fun k g => ?_⟩` and prove the remaining obligations. Take `⟨u', hu', m, k, gf, rfl⟩` from `GlobalTheory.IwasawaAdelic.iwasawa E (fun _ => a) H g'`. Establish `e : ∀ X Y Z W : GA E (r + s), X * (Y * Z * W) = X * Y * Z * W` using `fun _ _ _ _ => by simp only [mul_assoc]`.

Rewrite using `[e, key _ (mul_mem hu hu'), key _ hu']`. Take `⟨n, F₁, F₂, hF₁, hF₂, hΦ⟩` from `hsl k g`. Establish `hmem : ∀ i, (fun m : Fin (d₁ + d₂) → GA E a => (F₁ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₁ => a) h₁) (fun b => m (Fin.castAdd d₂ b))) * (F₂ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₂ => a) h₂) (fun b => m (Fin.natAdd d₁ b)))) ∈ tensorForms (n` using `fun _ => a) fam := by`. Introduce `i`. Establish `e₁ : (fun b => fam (Fin.castAdd d₂ b)) = fun b => (fam₁ b).twist (Model.absC E z₁)` using `funext he₁`.

Establish `e₂ : (fun b => fam (Fin.natAdd d₁ b)) = fun b => (fam₂ b).twist (Model.absC E z₂)` using `funext he₂`. Use `tensorForms_append fam (G₁ := fun m₁ => (F₁ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₁ => a) h₁) m₁)) (G₂ := fun m₂ => (F₂ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₂ => a) h₂) m₂)) ?_ ?_` and prove the remaining obligations. Rewrite using `[e₁]`. Conclude with `tw_slice_mem (hF₁ i)`. Rewrite using `[e₂]`.

Conclude with `tw_slice_mem (hF₂ i)`. Use `Submodule.sum_mem _ (fun i _ => hmem i) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `m`. Rewrite using `[Finset.sum_apply, leviEmb_split h₁ h₂ H, hΦ]`.
-/
theorem mem_indForms_of_slices (h₁ : ∑ _ : Fin d₁, a = r) (h₂ : ∑ _ : Fin d₂, a = s) (H : ∑ _ : Fin (d₁ + d₂), a = r + s)
    {fam₁ : Fin d₁ → CuspSub E a} {fam₂ : Fin d₂ → CuspSub E a} {fam : Fin (d₁ + d₂) → CuspSub E a} {z₁ z₂ : ℂ}
    (he₁ : ∀ b, fam (Fin.castAdd d₂ b) = (fam₁ b).twist (Model.absC E z₁))
    (he₂ : ∀ b, fam (Fin.natAdd d₁ b) = (fam₂ b).twist (Model.absC E z₂)) {Φ : Sm E (r + s)}
    (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, Φ.1 (unip x * g) = Φ.1 g)
    (hsl : ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)), ∃ (n : ℕ) (F₁ : Fin n → Sm E r) (F₂ : Fin n → Sm E s),
      (∀ i, F₁ i ∈ tw (indForms h₁ fam₁) z₁) ∧ (∀ i, F₂ i ∈ tw (indForms h₂ fam₂) z₂) ∧
      ∀ m : GA E r × GA E s, Φ.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        ∑ i, (F₁ i).1 m.1 * (F₂ i).1 m.2)
    (hsm : Φ ∈ GlobalTheory.PRep.smoothPart (finRep E (r + s))) (hfv : Φ ∈ finVec (cptRep E (r + s))) :
    Φ ∈ indForms H fam := by
  have key : ∀ w ∈ unipRad (Ad E) (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H), ∀ (m : Fin (d₁ + d₂) → GA E a)
      (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)),
      Φ.1 (w * leviEmb (Ad E) (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) m *
        (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
      Φ.1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) m *
        (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) := by
    intro w hw m k g
    obtain ⟨x, w₁, w₂, hw₁, hw₂, rfl⟩ := unipRad_split h₁ h₂ H hw
    obtain ⟨n, F₁, F₂, hF₁, hF₂, hΦ⟩ := hsl k g
    rw [leviEmb_split h₁ h₂ H, mul_assoc (unip x), ← map_mul, Prod.mk_mul_mk, mul_assoc, hu, hΦ, hΦ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tw_unip_inv (hF₁ i) w₁ hw₁, tw_unip_inv (hF₂ i) w₂ hw₂]
  refine ⟨fun u hu g' => ?_, hsm, hfv, fun k g => ?_⟩
  · obtain ⟨u', hu', m, k, gf, rfl⟩ := GlobalTheory.IwasawaAdelic.iwasawa E (fun _ => a) H g'
    have e : ∀ X Y Z W : GA E (r + s), X * (Y * Z * W) = X * Y * Z * W := fun _ _ _ _ => by simp only [mul_assoc]
    rw [e, key _ (mul_mem hu hu'), key _ hu']
  · obtain ⟨n, F₁, F₂, hF₁, hF₂, hΦ⟩ := hsl k g
    have hmem : ∀ i, (fun m : Fin (d₁ + d₂) → GA E a =>
        (F₁ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₁ => a) h₁) (fun b => m (Fin.castAdd d₂ b))) *
        (F₂ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₂ => a) h₂) (fun b => m (Fin.natAdd d₁ b)))) ∈
          tensorForms (n := fun _ => a) fam := by
      intro i
      have e₁ : (fun b => fam (Fin.castAdd d₂ b)) = fun b => (fam₁ b).twist (Model.absC E z₁) := funext he₁
      have e₂ : (fun b => fam (Fin.natAdd d₁ b)) = fun b => (fam₂ b).twist (Model.absC E z₂) := funext he₂
      refine tensorForms_append fam
        (G₁ := fun m₁ => (F₁ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₁ => a) h₁) m₁))
        (G₂ := fun m₂ => (F₂ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₂ => a) h₂) m₂)) ?_ ?_
      · rw [e₁]; exact tw_slice_mem (hF₁ i)
      · rw [e₂]; exact tw_slice_mem (hF₂ i)
    convert Submodule.sum_mem _ (fun i _ => hmem i) using 1
    funext m
    rw [Finset.sum_apply, leviEmb_split h₁ h₂ H, hΦ]

end PositivityTheory.Rg.Rs.InductionInStages

end
