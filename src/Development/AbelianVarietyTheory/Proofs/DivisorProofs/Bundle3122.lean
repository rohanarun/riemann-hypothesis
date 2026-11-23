module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3119
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2989
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphLieConditionOfDirections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueLie

section Core

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]


set_option maxHeartbeats 4000000 in
theorem core (hA : IsAbelianScheme A₀) {O : Type} [CommRing O] (act : O → (A₀ ⟶ A₀)) [∀ c, IsMonHom (act c)]
    (ρ' : O →+* Module.End k (HdR A₀)) (hρ' : ∀ c h, ρ' c h = push (dp0 k) (𝟙 _) (act c) h)
    (ω : O) (r : k) {a : ℕ} (χ : Fin a → O → k) (hχ : ∀ i i', i ≠ i' → ∃ c, χ i c ≠ χ i' c)
    {d : ℕ} (hd : 0 < d) (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (E' : Fin d → Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hE : ∀ j e, e ∈ E' j ↔ (fstC A₀ e ∈ Fil A₀ ∧ (sndC A₀ e : HdR A₀) - f j (fstC A₀ e) ∈ Fil A₀))
    (hlift : ∀ j, ∀ x ∈ Fil A₀, ∃ e ∈ E' j, fstC A₀ e = x ∧ (sndC A₀ e : HdR A₀) = f j x)
    (hstab : ∀ j c, ∀ e ∈ E' j,
      push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act c) e ∈ E' j)
    (hlie : ∀ j e, push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act ω) e -
        algebraMap k (TrivSqZeroExt k k) r • e ∈ E' j →
      ∃ w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀,
        (∀ i c, push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act c) (w i) -
          algebraMap k (TrivSqZeroExt k k) (χ i c) • w i ∈ E' j) ∧ e - ∑ i, w i ∈ E' j)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (he : push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
        (act ω) e - algebraMap k (TrivSqZeroExt k (Fin d → k)) r • e ∈ GlobalTheory.HTGlue.glueFil A₀ f) :
    ∃ w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
        (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀,
      (∀ i c, push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
          (act c) (w i) - algebraMap k (TrivSqZeroExt k (Fin d → k)) (χ i c) • w i ∈ GlobalTheory.HTGlue.glueFil A₀ f) ∧
        e - ∑ i, w i ∈ GlobalTheory.HTGlue.glueFil A₀ f := by
  rw [push_sub_mem_glueFil_iff] at he
  obtain ⟨he1, he2⟩ := he

  choose ee hee1 hee2 using fun j : Fin d ↦ exists_of_coords (V := k) hA (fstC A₀ e)
    (LinearMap.proj j ∘ₗ sndC A₀ e)
  have hEj : ∀ j, push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act ω) (ee j) -
      algebraMap k (TrivSqZeroExt k k) r • ee j ∈ E' j := fun j ↦ by
    rw [push_sub_mem_iff (f j) (E' j) (hE j), hee1, hee2]
    exact ⟨he1, he2 j⟩
  choose W hW1 hW2 using fun j ↦ hlie j (ee j) (hEj j)
  have hα := fun j i c ↦ (push_sub_mem_iff (f j) (E' j) (hE j) _ _ _).1 (hW1 j i c)
  have hs : ∀ j, fstC A₀ e - ∑ i, fstC A₀ (W j i) ∈ Fil A₀ ∧
      ((LinearMap.proj j ∘ₗ sndC A₀ e : HdR A₀) - ∑ i, (sndC A₀ (W j i) : HdR A₀)) -
        f j (fstC A₀ e - ∑ i, fstC A₀ (W j i)) ∈ Fil A₀ := fun j ↦ by
    have := (sub_sum_mem_iff (f j) (E' j) (hE j) _ _).1 (hW2 j)
    rwa [hee1, hee2] at this

  have hfstab : ∀ j c, ∀ x ∈ Fil A₀,
      push (dp0 k) (𝟙 _) (act c) (f j x) - f j (push (dp0 k) (𝟙 _) (act c) x) ∈ Fil A₀ := by
    intro j c x hx
    obtain ⟨e1, he1E, h1, h2⟩ := hlift j x hx
    have := ((push_mem_iff (f j) (E' j) (hE j) (act c) e1).1 (hstab j c e1 he1E)).2
    rwa [h1, h2] at this

  let j₀ : Fin d := ⟨0, hd⟩
  have hFst : ∀ c, ∀ x ∈ Fil A₀, ρ' c x ∈ Fil A₀ := fun c x hx ↦ by rw [hρ']; exact push_mem_Fil _ hx
  have hglue : ∀ j i, fstC A₀ (W j i) - fstC A₀ (W j₀ i) ∈ Fil A₀ := fun j ↦
    GlobalTheory.T.components_mem_of_sum_mem_distinct_eigencharacters_mod k (HdR A₀) O ρ' (Fil A₀) hFst a χ hχ (fun i ↦ fstC A₀ (W j i) - fstC A₀ (W j₀ i))
      (fun i c ↦ by
        rw [hρ', map_sub, smul_sub, sub_sub_sub_comm]; exact sub_mem (hα j i c).1 (hα j₀ i c).1)
      (by
        rw [Finset.sum_sub_distrib]
        have := sub_mem (hs j₀).1 (hs j).1
        convert this using 1
        abel)

  choose w hw1 hw2 using fun i ↦ exists_of_coords (V := Fin d → k) hA (fstC A₀ (W j₀ i))
    (LinearMap.pi fun j ↦ (sndC A₀ (W j i) : HdR A₀) + f j (fstC A₀ (W j₀ i) - fstC A₀ (W j i)))
  refine ⟨w, fun i c ↦ ?_, ?_⟩
  · rw [push_sub_mem_glueFil_iff, hw1, hw2]
    refine ⟨(hα j₀ i c).1, fun j ↦ ?_⟩
    rw [LinearMap.proj_pi]
    have hδ : fstC A₀ (W j₀ i) - fstC A₀ (W j i) ∈ Fil A₀ := by
      have := neg_mem (hglue j i); rwa [neg_sub] at this
    have := add_mem (hα j i c).2 (hfstab j c _ hδ)
    convert this using 1
    simp only [map_add (f := _), map_sub, map_smul, smul_add, smul_sub]
    abel
  · rw [sub_sum_mem_glueFil_iff]
    simp only [hw1, hw2, LinearMap.proj_pi]
    refine ⟨(hs j₀).1, fun j ↦ ?_⟩
    convert (hs j).2 using 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_add_distrib, map_sub, map_sum, Finset.sum_sub_distrib]
    abel

end Core


set_option maxHeartbeats 1000000 in
theorem lie_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ), 0 < d → ∀ (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → (∀ j, ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - ((algebraMap k (TrivSqZeroExt k k)).comp tk) b.ρ • e ∈ E' j → ∃ w : Fin D.a → Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - ((algebraMap k (TrivSqZeroExt k k)).comp tk) (b.t i c) • w i ∈ E' j) ∧ e - ∑ i, w i ∈ E' j) → ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk) b.ρ • e ∈ GlobalTheory.HTGlue.glueFil o₀.A f → ∃ w : Fin D.a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk) (b.t i c) • w i ∈ GlobalTheory.HTGlue.glueFil o₀.A f) ∧ e - ∑ i, w i ∈ GlobalTheory.HTGlue.glueFil o₀.A f := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d hd f E' hcompl hred hlift hstab hlie e he
  haveI hact : ∀ c : 𝓞 D.F, IsMonHom (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) := fun c ↦ o₀.act.hom _
  have L1j := fun j ↦ GlobalTheory.T.dualNumber_hodge_summand_eq_graph_coordinates k o₀.A o₀.ab (f j) (E' j) (hcompl j) (hred j) (hlift j)
  have hχ : ∀ i i', i ≠ i' → ∃ c : 𝓞 D.F, tk (b.t i c) ≠ tk (b.t i' c) := by
    intro i i' hii'
    by_contra hcon
    push_neg at hcon
    have hle : Ideal.span (Set.range fun x ↦ b.t i x - b.t i' x) ≤ RingHom.ker tk := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, hcon x, sub_self]
    have h1 : (1 : R) ∈ RingHom.ker tk := hle (b.comax i i' hii' ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hlift' : ∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, fstC o₀.A e = x ∧ (sndC o₀.A e : HdR o₀.A) = f j x := by
    intro j x hx
    obtain ⟨e1, he1, h⟩ := hlift j x hx
    refine ⟨e1, he1, ?_, ?_⟩ <;> ext c
    · rw [fstC_apply, h c, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · rw [sndC_apply, h c, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact core o₀.ab (fun c : 𝓞 D.F ↦ o₀.act.act (algebraMap (𝓞 D.F) D.O c))
    ((GlobalTheory.HTCount.crysAct o₀).comp (algebraMap (𝓞 D.F) D.O)) (fun _ _ ↦ rfl) D.ω (tk b.ρ)
    (fun i c ↦ tk (b.t i c)) hχ hd f E' L1j hlift' (fun j c e he ↦ hstab j _ e he) hlie e he

end GlobalTheory.HTGlueLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleRootsAndEvaluation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_roots_and_evaluation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ (ζ : ℕ → kˣ) (ev : ℕ → D.La → (Over.mk x ⟶ o.A)), (∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) ∧ (∀ e, ζ (e + 1) ^ p = ζ e) ∧ (∀ e y z, ev e (y + z) = ev e y * ev e z) ∧ (∀ e (c : D.O) y, ev e (c • y) = ev e y ≫ o.act.act c) ∧ (∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ e (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q) ∧ (∀ e y, ev (e + 1) y ^ p = ev e y) ∧ (∀ e y z, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e) (ev e y) (ev e z) (unitOn (ζ e ^ (2 * D.EF y z)))) := by
  first | (exact @GlobalTheory.UPel.HT.PadicTate.exists_padic_similitude) | (exact GlobalTheory.UPel.HT.PadicTate.exists_padic_similitude) | (intros; apply GlobalTheory.UPel.HT.PadicTate.exists_padic_similitude <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemeHomCompEqMulOfKerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualAbelianScheme_hom_comp_eq_mul_of_ker : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  first | (exact @GlobalTheory.DualFactor.main) | (exact GlobalTheory.DualFactor.main) | (intros; apply GlobalTheory.DualFactor.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerChartOfHeatOperators
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ChartKSBracket

theorem exists_derivation_intAlgebra' {A : Type} [CommRing A] (inst : Algebra ℤ A) (D : @Derivation ℤ A A _ _ _ inst _ _) :
    ∃ D' : @Derivation ℤ A A _ _ _ (Ring.toIntAlgebra A) _ _, ⇑D' = ⇑D := by
  obtain rfl : inst = Ring.toIntAlgebra A := Subsingleton.elim _ _
  exact ⟨D, rfl⟩

theorem exists_isKS_of_heat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (O : Type) [CommRing O] [StarRing O] [Module O P.D.toPre.X] (oa : P.D.toPre.OAct O) (Y : Ray oa) (n : ℕ) (vY : Module.Basis (Fin n) (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vY a) (dd a)) → ∀ D : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i}) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∃ v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) ∧ IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) (h.Θ.map (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab O _ _ _ oa Y n vY dd hdd D hD h hbas hdef
  have hA := GlobalTheory.MumfordChart.admissibleBase_chartRing k m d
  haveI : IsNoetherianRing (ChartRing k m d) := hA.1
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) := hA.2.2.2
  letI := H.starRing
  have hne : ∀ i, bdParam k m d i ≠ 0 := fun i h0 => by
    have h4 := congrArg (fun f : ChartRing k m d => MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1) f) h0
    simp [bdParam, MvPowerSeries.coeff_X] at h4
  obtain ⟨ρ, hρ⟩ := GlobalTheory.TorusModel.exists_ringAct GlobalTheory.allSixLaws.1.globalFns P.oD (Φ := Y.Φ) Y.rep
  let Y' : Ray P.oD := { H := Y.H, Φ := Y.Φ, isGt := Y.isGt, rep := Y.rep, ρ := ρ, smul := hρ }
  choose v' hv' using fun a => tanPt E H (ChartRing k m d) t P Y' (vY a)
  refine ⟨fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) ≫ (tv (v' a)).left,
    fun a => isTanAtG_tv E H _ t (v' a), ?_⟩
  obtain ⟨D', hD'⟩ := exists_derivation_intAlgebra' _ D
  have key := GlobalTheory.T.kodairaSpencer_of_commuting_heat_operators_raynaud E H (ChartRing k m d) t P m (bdParam k m d) gam hmon hne hab Y' n vY dd hdd v' hv' D'
  rw [hD'] at key
  exact key h hbas hdef

end GlobalTheory.ChartKSBracket
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusKernelKilledSymmetricBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledLocus

theorem exists_open_kerKilled_locus : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → ∀ (T : Over V.toScheme) (x : T ⟶ (Over.pullback V.ι).obj G), (∃ s : ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (snd ((Over.pullback V.ι).obj G) T ≫ x) (fst ((Over.pullback V.ι).obj G) T)).left).Gen, s.IsGen) → x ^ d = 1) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → Set.range g.base ⊆ (U : Set S') := by
  intro d S' _ G _ _ P hG hP h1 h2 hs
  refine ⟨sSup {V | GlobalTheory.KerKilledLocus.KerKilledOn d G P V}, ?_, ?_⟩
  · intro V hV
    refine GlobalTheory.T.kernelKilledOverOpen_of_local d S' G P V ?_
    intro p hp
    obtain ⟨W, hW, hpW⟩ := (TopologicalSpace.Opens.mem_sSup).1 (hV hp)
    exact ⟨W, hpW, hW⟩
  · intro T g A' _ _ φ φ₂ P' hpb hsq hP' hiso hu hamp hker
    rintro _ ⟨t, rfl⟩
    obtain ⟨V, hV, hK⟩ := GlobalTheory.T.exists_open_kernel_killed_near_point d S' G P hG hP h1 h2 hs T g A' φ φ₂ P' hpb hsq hP' hiso hu hamp hker t
    exact (TopologicalSpace.Opens.mem_sSup).2 ⟨V, hK, hV⟩

end GlobalTheory.KerKilledLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingTwoPointsAmple
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.PairStep.exists_sec_separating_two_points_of_ample : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  intro hP hNV hNef X _ _ _ p n hproj hdim M Δ m G N ρ h x₁ x₂ hM hΔ hklt hm hlc hNamp hnum
    hx₁ hx₂ hne hh hvol hsum
  set S : ℚ := ∑ e ∈ Finset.Icc 1 n, h e with hS
  set ε : ℚ := (ρ - S) / (n + 1) with hε
  have hn1 : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hεpos : 0 < ε := div_pos (by linarith) hn1
  have h1 : ((n : ℚ) + 1) * ε = ρ - S := by rw [hε]; field_simp
  have hsplit : ∑ e ∈ Finset.Icc 1 n, (h e + ε) = S + n * ε := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp [hS]
  obtain ⟨D, d, hd, hQ, hcase⟩ := GlobalTheory.T.twoPoint_induction_kltPair_separation hP hNV hNef X p n hproj hdim Δ m G N ε h x₁ x₂
    hΔ hklt hm hlc hNamp hx₁ hx₂ hne hh hvol hεpos
  have hdρ : d < ρ := by
    have h2 : (n : ℚ) * ε + ε = ρ - S := by rw [← h1]; ring
    linarith
  rcases hcase with ⟨hlc1, hnk2⟩ | ⟨hlc2, hnk1⟩
  · obtain ⟨s, hs1, hs2⟩ := GlobalTheory.T.exists_separatingSection_of_isolatedNonKltPoint hNV X p n hproj hdim M Δ m G N D ρ d x₁ x₂ hM hΔ hm hlc
      hNamp hnum hQ hdρ hx₁ hne hlc1 hnk2
    exact ⟨s, Or.inl ⟨hs1, hs2⟩⟩
  · obtain ⟨s, hs2, hs1⟩ := GlobalTheory.T.exists_separatingSection_of_isolatedNonKltPoint hNV X p n hproj hdim M Δ m G N D ρ d x₂ x₁ hM hΔ hm hlc
      hNamp hnum hQ hdρ hx₂ (Ne.symm hne) hlc2 hnk1
    exact ⟨s, Or.inr ⟨hs2, hs1⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryThetaSetupIdealOverComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.UPoinc.exists_uSetup_ideal_over_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∃ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = A ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) ∧ UValThru Xo c C.i X₁.π Set.univ φ J₁ ι := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C A hAc hAi hAm
  obtain ⟨η, hη, hcl⟩ := GlobalTheory.UPoinc.exists_genericPoint_closure_eq_of_isClopen E H Dw hpq l Xo c C A hAc hAi hAm
  obtain ⟨X₁, -, hpr, hX₁⟩ := GlobalTheory.UPoinc.GSetup.exists_uSetup_proj E H Dw hpq l Xo c C η hη 0
  have hr := GlobalTheory.UPoinc.USetup.range_π_eq E H Dw hpq l Xo c C X₁ η A hX₁ hcl
  obtain ⟨ι, Y, πY, D, hι, hhom, hprop, hnY, hsupp, hord⟩ := _root_.GlobalTheory.UPoinc.exists_zhModel_effCartier_orders E H Dw hpq φ hφ l Xo c C X₁ hpr
  obtain ⟨ι', J₁, hι', hsupp', hord'⟩ := _root_.GlobalTheory.UPoinc.DescentPow.exists_idealSheaf_comap_uValThru E H Dw hpq φ hφ l Xo c C X₁ ι Y πY D hι hhom hprop hnY hsupp hord
  obtain ⟨hs, ho⟩ := GlobalTheory.UPoinc.ideal_orders_of_proper_model E H Dw hpq φ hφ l Xo c C X₁ Y πY hhom hprop ι' J₁ hsupp' hord'
  exact ⟨X₁, ι', J₁, hι', hr, hs, ho⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedKernelIsogenyTangentInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerUnram

theorem formallyUnramified_ker : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : AbVar K) (f : B ⟶ B), IsIsogeny f → (∀ v : epsPtR (𝟙 (Sp K)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left → v ≫ Hom.hom f = 1 → v = 1) → FormallyUnramified (pullback.snd (Hom.hom f).left η[B.X].left) := by
  intro K _ _ B f hf H
  have hfin : IsFinite (Hom.hom f).left := hf.1
  set Z := pullback (Hom.hom f).left η[B.X].left with hZ
  set p : Z ⟶ Sp K := pullback.snd (Hom.hom f).left η[B.X].left with hp
  have : IsFinite p := inferInstance
  have : IsAffine Z := isAffine_of_isAffineHom p
  have hnat := Scheme.isoSpec_hom_naturality p
  have hS : Spec.map p.appTop = Z.isoSpec.inv ≫ p ≫ (Sp K).isoSpec.hom := by
    rw [← hnat]; simp
  have hfinS : IsFinite (Spec.map p.appTop) := by rw [hS]; infer_instance
  have hfinR : p.appTop.hom.Finite := (IsFinite.SpecMap_iff _).1 hfinS
  let ψ : CommRingCat.of K ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop
  let _ : Algebra K Γ(Z, ⊤) := ψ.hom.toAlgebra
  have : Module.Finite K Γ(Z, ⊤) := by
    have h : ψ.hom.Finite := by
      show (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).Finite
      exact hfinR.comp (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
    exact h
  have hp' : p.appTop = (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ ψ := by simp [ψ]
  have : IsAffine (𝟙_ (Over (Sp K))).left := inferInstanceAs (IsAffine (Sp K))
  rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified), hp',
    CommRingCat.hom_comp, RingHom.RespectsIso.cancel_left_isIso RingHom.FormallyUnramified.respectsIso]
  show Algebra.FormallyUnramified K Γ(Z, ⊤)
  refine GlobalTheory.T.formally_unramified_of_dual_numbers K Γ(Z, ⊤) fun φ r => ?_

  let q : Sp (DualNumber K) ⟶ Z := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Z.isoSpec.inv
  have hq : q ≫ p = spMap (algebraMap K (DualNumber K)) := by
    have e := Scheme.isoSpec_inv_naturality p
    simp only [q, Category.assoc]
    rw [← e, Scheme.isoSpec_Spec]
    simp only [Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    exact φ.commutes a
  have hfst : ∀ {T : Scheme} (g : T ⟶ Z), (g ≫ pullback.fst (Hom.hom f).left η[B.X].left) ≫ B.X.hom = g ≫ p := by
    intro T g
    rw [Category.assoc, ← Over.w (Hom.hom f), ← Category.assoc (pullback.fst _ _), pullback.condition,
      Category.assoc, Over.w η[B.X]]
    rfl
  let v : epsPtR (𝟙 (Sp K)) ⟶ B.X := Over.homMk (q ≫ pullback.fst _ _) (by
    rw [hfst, hq]; exact (Category.comp_id _).symm)
  have hv : v ≫ Hom.hom f = 1 := by
    ext1
    rw [Over.comp_left, Hom.one_def, Over.comp_left]
    simp only [v, Over.homMk_left, Category.assoc]
    rw [pullback.condition, ← Category.assoc q, hq]
    rfl

  let T₀ : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let red : T₀ ⟶ epsPtR (𝟙 (Sp K)) := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, ← Spec.map_id]
    congr 1)
  let bas : epsPtR (𝟙 (Sp K)) ⟶ T₀ := Over.homMk (spMap (algebraMap K (DualNumber K))) rfl
  have hrb : red ≫ bas = 𝟙 T₀ := by
    ext1
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  let w : epsPtR (𝟙 (Sp K)) ⟶ B.X := v * (bas ≫ red ≫ v)⁻¹
  have hw₀ : red ≫ w = 1 := by
    simp only [w]
    rw [comp_mul, GrpObj.comp_inv, ← Category.assoc red bas, hrb, Category.id_comp, mul_inv_cancel]
  have hwf : w ≫ Hom.hom f = 1 := by
    simp only [w]
    rw [mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, hv, comp_one, comp_one, inv_one,
      _root_.mul_one]
  have hw : w = 1 := H w (by
    have := congrArg Over.Hom.left hw₀
    rw [Over.comp_left] at this
    exact this) hwf
  have hvc : v = bas ≫ red ≫ v := mul_inv_eq_one.mp hw
  have hq2 : q = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ q := by
    refine pullback.hom_ext ?_ ?_
    · have := congrArg Over.Hom.left hvc
      simpa [v, red, bas] using this
    · change q ≫ p = _ ≫ _ ≫ q ≫ p
      rw [hq, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
  simp only [q, ← Category.assoc] at hq2
  rw [cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at hq2
  have := congrArg TrivSqZeroExt.snd congr($(Spec.map_injective hq2).hom r)
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.KerUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorAuxiliarySymplecticLevelRepresentabl
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem harrisTaylorModuli_symplecticLevel_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SDRep (Module.finrank ℤ D.La / 2) M e → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M := by
  intro p _ D R _ _ b N M e hN hNp hM hMo hMp hep _ hdual hSD
  obtain ⟨X, s, u, hku, -, hqs, huniv⟩ := hSD
  have hMR : IsUnit ((M : ℕ) : R) := b.unit M hMp
  have hqP : IsQProjOver (𝟙 _ ≫ pullback.snd (s ≫ spMap (Int.castRingHom (cycAway M)))
      (spMap (Int.castRingHom R))) :=
    GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback M R hMR X s hqs _ (𝟙 _) inferInstance
  rw [Category.id_comp] at hqP
  have hLN := _root_.GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth R _ _ hqP
  obtain ⟨Z, π, v, lev, hlev, hfin, hfwd, hback⟩ :=
    GlobalTheory.T.harrisTaylor_structures_representable_siegel_baseChange p D R b N (Module.finrank ℤ D.La / 2) M e hN hNp hM hMo hMp hep X s u hku hLN
  refine ⟨Z, π ≫ pullback.snd _ _, π ≫ pullback.fst _ _ ≫ s, v, lev, hlev,
    GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback M R hMR X s hqs Z π hfin, ?_⟩
  intro S t t₁ o l hl
  have heS : IsUnit ((e : ℕ) : Γ(S, ⊤)) := by
    have h := (b.unit e hep).map ((t.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using h
  obtain ⟨f₀, ⟨hf₀s, hf₀pb⟩, hf₀u⟩ :=
    huniv S t₁ (o.toSieg hl) heS (GlobalTheory.T.harrisTaylor_siegelObject_polarisationKernel_killed p D R b N S t o _ M t₁ l hl e hep hdual)
  obtain ⟨g, ⟨hg₁, hg₂, hgm⟩, hgu⟩ := hback S f₀ t t₁ o l hl hf₀pb
  refine ⟨g, ⟨hg₂, ?_, hgm⟩, ?_⟩
  · rw [← hf₀s, ← hg₁]
    simp only [Category.assoc]
  · rintro g' ⟨hg's, hg's₁, hg'm⟩
    have hfst : g' ≫ π ≫ pullback.fst _ _ = f₀ :=
      hf₀u _ ⟨by simpa only [Category.assoc] using hg's₁, hfwd S g' t t₁ o l hl hg'm⟩
    exact hgu g' ⟨hfst, hg's, hg'm⟩

end GlobalTheory.UPel.HT
end
end

