module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0008
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0010
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SplitBCOfGalIso
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BcAll
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
open Polynomial
namespace GlobalTheory.CutAtGood
section AtPlace
attribute [local instance] Formalism.BasicNotions.Examples₂.NZ.neZero_g Formalism.BasicNotions.Examples₂.NZ.fact_g Classical.propDecidable
variable (D : D7)
end AtPlace
section OnMt
variable (D : D7) (μ : D.what₂.Tup) (j : ℕ)
end OnMt
section Record
variable {D : D7}
theorem isBCV_of_isBCV_of_same_ptV (hT0 : SumRepresentations.tie0 D) (hG : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : SumRepresentations.adm5 D) (hBC : SumRepresentations.adm1 D) {i : D.nd.Loc}
    {x : D.nd.X i} {P0 PI : D.naut.AV i} (h0 : D.naut.ptV i P0 = some x) (hx : D.naut.ptV i PI = some x)
    {Pa0 : List (Part D.naut.CG)} (hB0 : IsBCV D.nd D.naut i P0 Pa0) : IsBCV D.nd D.naut i PI Pa0 := by
  obtain ⟨Pa, hPa⟩ := hBC i PI
  have hp := _root_.UpperTheory.GalS.bcPerm_alt D hT0 hG h5 i x P0 PI Pa0 Pa h0 hx hB0 hPa
  exact isBCV_perm hPa hp.symm
end Record
section Series
variable {D : D7}
end Series
section Main
end Main
theorem main_alt_alt : ∀ (D : D7) (P : Pend D), GlobalTheory.TypeLeaf.SerLoc D → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → EigSpan P → CentralElt D → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i, ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i), CutAt i k π Xs β b ∧ TypeLocus P i k Xs := by
  intro D P hSer hBC hLGC hT0 h5 hEig hCE i k hl π hπ
  classical
  obtain ⟨hπZN, Sig, hSig, hgood⟩ := (D.Zgood_tie i π).1 hπ
  obtain ⟨σ', hσ'⟩ := P.Par_surj i π Sig hSig
  obtain ⟨P0, hP0, hB0⟩ := hSig
  let s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X] := fun kv => D.ntypes.labPar kv.1 σ' kv.2
  obtain ⟨z, L, hLnd, hLall, hz⟩ := hCE i s
  have onMt_coe (μ : D.what₂.Tup) (j : ℕ) (c : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
      D.ntypes.onMt μ j (c : MonoidAlgebra ℂ (G0g D.nd)) = D.ntypes.cenMt μ j c := by
    unfold NTypes.onMt
    rw [dite_eq_left c.2]
  have onMt_sum (μ : D.what₂.Tup) (j : ℕ) {ι : Type} (S : Finset ι)
      (a : ι → MonoidAlgebra ℂ (G0g D.nd))
      (ha : ∀ i ∈ S, a i ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) :
      D.ntypes.onMt μ j (∑ i ∈ S, a i) = ∑ i ∈ S, D.ntypes.onMt μ j (a i) := by
    induction S using Finset.induction_on with
    | empty =>
      unfold NTypes.onMt
      rw [Finset.sum_empty, Finset.sum_empty, dite_eq_left (Subalgebra.zero_mem _)]
      exact map_zero (D.ntypes.cenMt μ j)
    | insert i S hi ih =>
      have h₁ := ha i (Finset.mem_insert_self i S)
      have h₂ := Subalgebra.sum_mem (Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (fun x hx => ha x (Finset.mem_insert_of_mem hx))
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih (fun x hx => ha x (Finset.mem_insert_of_mem hx))]
      unfold NTypes.onMt
      rw [dite_eq_left (Subalgebra.add_mem _ h₁ h₂), dite_eq_left h₁, dite_eq_left h₂]
      exact map_add (D.ntypes.cenMt μ j) ⟨a i, h₁⟩ ⟨∑ x ∈ S, a x, h₂⟩
  let ef (s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X]) (kv : Σ k : Fin 2, D.nd.PlG k) : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) :=
    ⟨Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv)), atPlace_mem_center D kv.1 kv.2 _ (D.ntypes.eSer_central kv.1 (s kv))⟩
  have list_prod_eq (s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X])
      (L : List (Σ k : Fin 2, D.nd.PlG k)) (hnd : L.Nodup) (hall : ∀ kv, kv ∈ L) :
      (L.map fun kv => Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))).prod =
        ((∏ kv, ef s kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) := by
    have h1 : (L.map fun kv => Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))) =
        (L.map (ef s)).map (Subalgebra.val _) := by rw [List.map_map]; rfl
    have h2 : L.toFinset = Finset.univ := Finset.eq_univ_of_forall fun kv => List.mem_toFinset.2 (hall kv)
    rw [h1, ← map_list_prod (Subalgebra.val _), ← List.prod_toFinset (ef s) hnd, h2]
    rfl
  have cen_prod_fix {M : Type} [AddCommGroup M] [Module ℂ M]
      (cen : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) →ₐ[ℂ] Module.End ℂ M)
      {ι : Type} (e : ι → ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (S : Finset ι) (F : M) (h : ∀ a ∈ S, cen (e a) F = F) :
      cen (∏ a ∈ S, e a) F = F := by
    induction S using Finset.induction_on with
    | empty => rw [Finset.prod_empty, map_one]; rfl
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, map_mul, Module.End.mul_apply, ih (fun b hb => h b (Finset.mem_insert_of_mem hb)), h a (Finset.mem_insert_self a S)]
  have cen_prod_ne {M : Type} [AddCommGroup M] [Module ℂ M]
      (cen : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) →ₐ[ℂ] Module.End ℂ M)
      {ι : Type} [DecidableEq ι] (e : ι → ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (S : Finset ι) (F : M) (hne : cen (∏ a ∈ S, e a) F ≠ 0)
      (a : ι) (ha : a ∈ S) : cen (e a) F ≠ 0 := by
    intro h0
    apply hne
    rw [← Finset.prod_erase_mul S e ha, map_mul, Module.End.mul_apply, h0, map_zero]
  have hz' : ∀ F, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F := by
    intro F
    rw [hz, list_prod_eq s L hLnd hLall]
    rw [show (D.what₂.restRowsFiniteGroupCard : ℂ) • ((∏ kv, ef s kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
        MonoidAlgebra ℂ (G0g D.nd)) = (((D.what₂.restRowsFiniteGroupCard : ℂ) • ∏ kv, ef s kv :
          ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) from rfl,
      onMt_coe, map_smul]
    rfl
  have hfixπ : ∀ PI : D.naut.AV i, D.naut.ptV i PI = some π → ∀ F ∈ D.naut.typeV i PI,
      D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F = F := by
    intro PI hPI F hF
    have hB := _root_.GlobalTheory.CutAtGood.isBCV_of_isBCV_of_same_ptV hT0 hLGC h5 hBC hP0 hPI hB0
    have hF' := typeV_le_mtPar hσ' hB hF
    refine cen_prod_fix _ _ _ F fun kv _ => ?_
    rw [← onMt_coe]
    exact series_fix hSer i σ' F hF' kv.1 kv.2
  have hιb : iotaO D.nd D.naut i (D.what₂.restRowsFiniteGroupCard : D.nd.O i) = (D.what₂.restRowsFiniteGroupCard : ℂ) := map_natCast _ _
  have hscal : ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π,
      (P.zO i z).baseChange (FractionRing (D.nd.O i)) u = (D.what₂.restRowsFiniteGroupCard : D.nd.O i) • u :=
    hEig i z π _ fun PI hPI F hF => by rw [hz', hfixπ PI hPI F hF, hιb]
  let Xs : Set (D.nd.X i) :=
    {x | ∃ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, (P.zO i z).baseChange (FractionRing (D.nd.O i)) u ≠ 0}
  have hwit : ∀ x ∈ Xs, ∃ PI : D.naut.AV i, D.naut.ptV i PI = some x ∧ ∃ F ∈ D.naut.typeV i PI,
      ∀ kv, D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (ef s kv) F ≠ 0 := by
    rintro x ⟨u, hu, hne⟩
    by_contra hcon
    push Not at hcon
    apply hne
    have h0 := hEig i z x 0 (fun PI hPI F hF => ?_) u hu
    · rw [h0, zero_smul]
    · obtain ⟨kv, hkv⟩ := hcon PI hPI F hF
      rw [hz', map_zero, zero_smul]
      by_contra hc
      have hc' : D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F ≠ 0 := fun h => hc (by rw [h, smul_zero])
      exact cen_prod_ne _ _ _ F hc' kv (Finset.mem_univ kv) hkv
  have hcard : D.what₂.restRowsFiniteGroupCard ≠ 0 := by
    rw [D.nd.restN_card_levelGroup_eq]
    refine Finset.prod_ne_zero_iff.2 fun k' _ => ?_
    have : NeZero (D.host.g k') := ⟨(D.host.g_prime k').ne_zero⟩
    exact pow_ne_zero _ Nat.card_pos.ne'
  have hb0 : (D.what₂.restRowsFiniteGroupCard : D.nd.O i) ≠ 0 := by
    intro h
    have := congrArg (iotaO D.nd D.naut i) h
    rw [hιb, map_zero] at this
    exact (Nat.cast_ne_zero.2 hcard) this
  have hπX : π ∈ Xs := by
    have hpos : 0 < Module.finrank ℂ ↥(⨆ P ∈ {P | D.naut.ptV i P = some π}, D.naut.typeV i P) := by
      obtain ⟨P2, hP2⟩ := D.naut.pt_surj i π
      refine Nat.pos_of_ne_zero fun h0 => D.naut.typeV_ne i P2 ?_
      have hbot := Submodule.finrank_eq_zero.1 h0
      exact le_bot_iff.1 (hbot ▸ le_iSup₂_of_le (f := fun P _ => D.naut.typeV i P) P2 hP2 le_rfl)
    rw [← D.naut.eig_dim i π] at hpos
    have hne : heckeEig (D.nd.T i) (D.nd.act i) π ≠ ⊥ := by
      intro h
      have e : D.nd.mult i π = Module.finrank (FractionRing (D.nd.O i))
          ↥(heckeEig (D.nd.T i) (D.nd.act i) π) := rfl
      rw [e, h, finrank_bot] at hpos
      exact lt_irrefl 0 hpos
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨u, hu, ?_⟩
    rw [hscal u hu, ← algebraMap_smul (FractionRing (D.nd.O i))]
    refine smul_ne_zero ?_ hu0
    rw [Ne, ← map_zero (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))]
    exact (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))).ne hb0
  refine ⟨Xs, P.zO i z, (D.what₂.restRowsFiniteGroupCard : D.nd.O i), ⟨hπX, (D.Z_tie i π).2 hπZN, ?_, fun f => P.zO_comm i z f,
    hb0, hscal, fun x hx u hu => ?_, ?_⟩, ?_⟩
  · intro x hx hxZ
    obtain ⟨PI, hPI, F, hF, hne⟩ := hwit x hx
    obtain ⟨Sig1, hS1⟩ := hasParamX_of_Z hT0 h5 hxZ
    obtain ⟨σ1, hσ1⟩ := P.Par_surj i x Sig1 hS1
    obtain ⟨P1, hP1, hB1⟩ := hS1
    have hF1 := typeV_le_mtPar hσ1 (_root_.GlobalTheory.CutAtGood.isBCV_of_isBCV_of_same_ptV hT0 hLGC h5 hBC hP1 hPI hB1) hF
    have hlab : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), s kv = D.ntypes.labPar kv.1 σ1 kv.2 := fun kv =>
      hSer i σ1 kv.1 kv.2 (s kv) F hF1
        (by rw [show Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv)) = ((ef s kv : ↥(Subalgebra.center ℂ
          (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) from rfl, onMt_coe]; exact hne kv)
    have hg1 : goodSig D.nd D.naut Sig1 := goodSig_of_labels (fun k' v => by
      rw [← labPar_eq hσ' k' v, ← labPar_eq hσ1 k' v]; exact hlab ⟨k', v⟩) hgood
    exact (D.Zgood_tie i x).2 ⟨(D.Z_tie i x).1 hxZ, Sig1, ⟨P1, hP1, hB1⟩, hg1⟩
  · by_contra h
    exact hx ⟨u, hu, h⟩
  · rw [← hl]
    exact lenUnit_natCast_le i _ hcard
  · refine ⟨fun v => s ⟨k, v⟩, fun v => ?_, fun x hx => ?_⟩
    · show Squarefree (D.ntypes.labPar k σ' v) ∧ ∀ u : (ZMod (D.host.g k))ˣ,
          u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ → ¬ (D.ntypes.labPar k σ' v).IsRoot (u : ZMod (D.host.g k))
      rw [labPar_eq hσ' k v]
      exact good_labels hgood i k v
    · obtain ⟨PI, hPI, F, hF, hne⟩ := hwit x hx
      refine ⟨PI, hPI, fun v => ?_⟩
      have h1 := hne ⟨k, v⟩
      rw [← onMt_coe] at h1
      change D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k (s ⟨k, v⟩))) F ≠ 0 at h1
      have hc : ∀ τ ∈ (Finset.univ : Finset ((P.lz k).Irr D.R.r)),
          Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = s ⟨k, v⟩ then (P.lz k).idem τ else 0) ∈
            Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := by
        intro τ _
        split_ifs
        · exact atPlace_mem_center D k v _ fun b => (P.lz k).idem_central τ b
        · rw [atPlace_zero]
          exact Subalgebra.zero_mem _
      rw [P.eSer_eq k, atPlace_sum, onMt_sum _ _ _ _ hc, LinearMap.sum_apply] at h1
      obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      by_cases hlab : (P.lz k).lab τ = s ⟨k, v⟩
      · rw [if_pos hlab] at hτ
        exact ⟨τ, (P.kty_spec i PI k v τ).2 ⟨F, hF, hτ⟩, hlab⟩
      · exfalso
        apply hτ
        rw [if_neg hlab, atPlace_zero]
        unfold NTypes.onMt
        rw [dite_eq_left (Subalgebra.zero_mem _)]
        have e0 : (⟨0, Subalgebra.zero_mem _⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) = 0 := rfl
        rw [e0, map_zero]
        rfl
end GlobalTheory.CutAtGood
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefficientExtensionDecomposition
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_decomposition_of_good_galois_local : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → _root_.UpperTheory.GalS.G2a D.nd D.naut i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) ∧ ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  first | exact @_root_.GlobalTheory.CrysFromGTwo.main_alt_alt | exact _root_.GlobalTheory.CrysFromGTwo.main_alt_alt | (intros; apply _root_.GlobalTheory.CrysFromGTwo.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CutBoundOfSteps
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
noncomputable section
namespace GlobalTheory.Pass
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cutBound_of_steps_alt : _root_.GlobalTheory.Pass.NoCutStatement → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CT : ℕ), SumRepresentations.adm5 D → ElementDenominator.adm12 D → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → FontaineAtPlacesOverL (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT fun i k ρ eta => ∀ π ∈ D.nd.Zgood i, ∀ Xs : Set (D.nd.X i), π ∈ Xs → TypeLocus P i k Xs → LocalCongruenceBound CT eta i ρ π (vccCut i Xs π) := by
  rintro ⟨_hCI, _hCen, hDeg, hType, hPotD, hPotDu, hJD, hJDu, hLift, hSub, hCont, hLocD, hLocDu, hHf, hRes, hGlob⟩
  intro D P HW F CT h5 h12 hIne hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hTB hBK hBC hLGC hFont htie0 hChi
  obtain ⟨hDJ, hPDR, hPT, hBr, hIE⟩ := GlobalTheory.Closing.closing_at_record D
  intro i k k' _hkk' hlk r ρ hr hdec eta s S sg U hs _hlog hCT _hsg hHost hsFin hSha π hπ Xs hπXs hTL
  have hπZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  have hHG : HG D.nd D.naut i := GlobalTheory.EigenProjector.HG_of_mem_Zgood D i π hπ
  have hdecπ := hdec π hπZ
  have hTLGC : TypeLGC P := hType D P hDZ htie0 hBC hLGC h5
  have hPH : PairedCharacterCondition.tiePH (D := D) := D.loc_tie
  have hl2 : D.nd.l i ≠ 2 := hlk ▸ Formalism.L2.Pj.g_ne_two D k
  have hloc : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), HfChar i w hw ∧
      LocBoundP i w hw r Xs (WpO D.nd i ρ π) (2 * D.R.r * eMax D CT eta) ∧
      ∀ c ∈ Finset.Icc 1 D.R.t, LocBoundP i w hw r Xs (chiRatO D.nd i c) (2 * 1 * eMax D CT eta) := by
    intro w hw
    have hdeg1 := (hDeg D hBr i k hlk).2 w hw
    have hPot : PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) (D.R.nV + 1) :=
      hPotD D P hTLGC hFont htie0 hBr hPH hChi hIE h12 hPT hIne i k hlk r ρ hr π hπZ hdecπ Xs hπXs hTL w hw
    have hCT' : CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.nd.l i := hlk ▸ hCT
    have hH : eta + D.R.t + 1 < s + S := by omega
    have hsub := hSub D i r ρ hr π hdecπ Xs hπXs
    have key : ∀ (kk : ℕ) (M : GE D.nd →* Matrix (Fin kk) (Fin kk) (D.nd.O i)), SubTw i r Xs M →
        LocBoundP i w hw r Xs M (2 * kk * eMax D CT eta) := by
      intro kk M hM
      cases hsw : sg w
      · have hPotDu' := hPotDu D hPT i r hr Xs w hw _ hPot
        have hJ := hJDu D hDJ hPDR i r hr eta s S sg U hs hHost Xs w hw _ hsw hPot
        have hL := hLift D CT hT hFont i w hw hdeg1 (↥Xs) (fun x => rDuO D.nd i r x)
          (fun x => (hCont D i r hr x).2) eta (s + S) hH hCT' hPotDu' hJ
        exact hLocDu D hLOC hBK hFont hPDR i r hr Xs w hw hdeg1 _ _ hPot hL kk M hM
      · have hJ := hJD D i r eta s S sg U hs hHost Xs w hw hsw
        have hL := hLift D CT hT hFont i w hw hdeg1 (↥Xs) (fun x => rTwO D.nd i r x)
          (fun x => (hCont D i r hr x).1) eta (s + S) hH hCT' hPot hJ
        exact hLocD D hLOC hBK hFont hPDR i r hr Xs w hw hdeg1 _ _ hPot hL kk M hM
    exact ⟨hHf D P HW F hTB hIE i k hlk hl2 w hw hdeg1, key _ _ hsub.1, fun c hc => key _ _ (hsub.2 c hc)⟩
  have hG1 : TruncatedSeriesCountingIdentities.admG1 (D := D) i r := by
    intro g kk
    obtain ⟨f, hf⟩ := (hG14 i r hr).1 g kk
    have e : (fun x : D.nd.X i => ((rO D.nd i r x g).charpolyRev).coeff kk) = (f : D.nd.X i → D.nd.O i) :=
      funext fun x => (hf x).symm
    rw [e]
    exact f.2
  have hG4 : TruncatedSeriesCountingIdentities.admG4 (D := D) i r := by
    intro x v hl hS hQ g hg
    exact (hG14 i r hr).2.2.2 x v hl hS hQ (D.nd.plOm.1 v) (D.nd.plOm.2 v) g hg
  obtain ⟨S0, hS0, -⟩ := ((hN5g i k hlk hHG r ρ hr).2 π hπZ hdecπ).1 hπZ
  have hG := hGlob D i r ρ π Xs (2 * D.R.r * eMax D CT eta) (2 * 1 * eMax D CT eta) hr hG1
    (hRes D hRbar hG14 i r ρ hr π hπ hdecπ) hG4 (galois_condition_five_of D i r hG5 hHG hr)
    (GlobalTheory.TameDesign.main D i).2 (galois_condition_six_of D i r hG6 hHG hr) hdecπ (coefficient_compatibility_of D i (hBr i))
    ⟨S0, hS0⟩ hπZ hπXs hloc (hsFin π hπ) hSha
  have hcard : (placesOver D.host.E (D.nd.l i)).ncard = 2 * D.R.f := (hDeg D hBr i k hlk).1
  have hnat : (placesOver D.host.E (D.nd.l i)).ncard * (2 * D.R.r * eMax D CT eta + D.R.t * (2 * 1 * eMax D CT eta)) =
      D.R.f * (2 * ((2 * D.R.r + D.R.t * 2) * (CT * ((D.R.nV + 1) * ((D.R.nV + 1) ^ 2 / 4) +
        (eta + D.R.t + 1) * ((D.R.nV + 1) + (D.R.nV + 1) ^ 2 / 4))))) := by
    rw [hcard]; unfold eMax; ring
  rw [hnat] at hG
  have hrn : D.R.r ≤ D.R.nV := by unfold Ranks.nV; omega
  have hr2 : 2 ≤ D.R.r := hRbar.1
  refine ⟨D.R.nV + 1, (D.R.nV + 1) ^ 2 / 4, by omega, le_refl _, ?_, Nat.mul_div_le _ _, ?_⟩
  · have h9 : 9 ≤ (D.R.nV + 1) ^ 2 := by nlinarith
    omega
  · have hG' := (Rat.cast_le (K := ℝ)).2 hG
    push_cast at hG' ⊢
    linarith
end GlobalTheory.Pass
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigPdHolds
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology
open GlobalTheory.TameEig
noncomputable section
namespace UpperTheory.GalS
theorem eigPd_holds_alt : _root_.GlobalTheory.TameEig.eigPd_holds_tyz := by
  intro D hA hLGC _ i _ w hS hw rb hrb hroot
  have hC : Formalism.MainNotions.SumRepresentations.Cheb D.nd := hA.2.2.2.2.2.2.2.2.1
  have hDel := Formalism.MainNotions.SumRepresentations.Del_holds D i
  have hq : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    · exact D.host.pde'_prime
    · exact D.host.pde_prime
  have hq15 : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) % 15 = 1 := by
    split_ifs
    · exact D.host.pde_mod.2
    · exact D.host.pde_mod.1
  have hne := residue_ne_one D.nd i w hS _ hq hq15 hw (hDel w hS hw)
  have hcond : w ∈ D.nd.Q i ∨ (Formalism.MainNotions.SumRepresentations.At.Del D.nd i ∧ (w ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ w ∈ placesOver D.host.E D.host.pde'))) := by
    refine Or.inr ⟨hDel, ?_⟩
    by_cases hlp : D.nd.l i = D.host.pde
    · rw [if_pos hlp] at hw
      exact Or.inr ⟨hlp, hw⟩
    · rw [if_neg hlp] at hw
      exact Or.inl hw
  have x : D.nd.X i := Classical.choice (D.nd.neX i)
  have hQ : ∀ x, ∃ ρ, Formalism.MainNotions.SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := fun x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hA.2.2.1 i P
    obtain ⟨ρ, h1, h2, h3, -⟩ := isoRep D hA.1 (_root_.UpperTheory.GalS.weak' hA.2.2.2.1) i P Pa hPa
    exact ⟨ρ, heckeQ D i x P Pa hP hPa ρ h1 h2 h3⟩
  choose rq hrq using hQ
  obtain ⟨r, hr⟩ := Formalism.MainNotions.SumRepresentations.exists_GoodR D.nd D.naut hA.2.1 i ⟨rq, hrq⟩
  have hL := hLGC i r hr w (Or.inl hS)
  have hs := _root_.Formalism.MainNotions.SumRepresentations.splitI_of_monodromyInertiaType_of_lgCatN D.nd r D.naut hr hA.2.2.2.2.2.1 w (Or.inl hS) hcond hL x
  have hg := D.nd.locNd_chebotarevPlace_mem i w
  have hwl := D.nd.SQ_l i w (Or.inl hS)
  have fac := Formalism.MainNotions.SumRepresentations.rhobar_fac D.nd r hC hr rb hrb x (D.nd.gam0 i w)
  rw [charpoly_red D.nd r hs _ hg] at fac
  have hprod : ∏ c ∈ Finset.Icc 1 D.R.t, (X - C (IsLocalRing.residue (D.nd.O i)
      ((D.nd.chi i c (D.nd.gam0 i w) : (D.nd.O i)ˣ) : D.nd.O i))) =
      ∏ _c ∈ Finset.Icc 1 D.R.t, (X - C (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)))) :=
    Finset.prod_congr rfl fun c hc => by
      rw [Formalism.MainNotions.SumRepresentations.character_eq_first_off_l D.nd w hwl c (Finset.mem_Icc.1 hc).1 (Finset.mem_Icc.1 hc).2 _ hg]
      rfl
  rw [hprod, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel] at fac
  have hcp := mul_right_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero _)) fac
  have h0 : ((X - 1 : Polynomial (IsLocalRing.ResidueField (D.nd.O i))) ^ D.R.r).eval
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) = 0 := by
    rw [← hcp]
    exact hroot
  rw [eval_pow, eval_sub, eval_X, eval_one] at h0
  exact pow_ne_zero _ (sub_ne_zero.2 hne) h0
end UpperTheory.GalS
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHubData
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX
theorem exists_canonical_hubData_with_bounds : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK), _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → ∀ (e' : FamilyRepresentationConstants.RFam D → FamilyRepresentationConstants.RhoFam D → D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ) (exc : FamilyRepresentationConstants.RhoFam D → Finset ℕ) (I : TwIn D), ∃ X : KillingConditions.HubData D, GlobalTheory.HubX.Canon L HW R X ∧ X.e' = e' X.r X.ρ ∧ X.exc = exc X.ρ ∧ X.I = I ∧ (∀ i, GoodR D.nd i (X.r i)) ∧ (0 ≤ L.etaSz → (X.eta : ℝ) ≤ 2 * L.etaSz) ∧ ∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i := by
  intro hC D L HW R h2 h41 e' exc I
  obtain ⟨r, ρ, h⟩ := GlobalTheory.PtCore.exists_ptFam hC D (_root_.GlobalTheory.T.galoisRepsCusp_of_adm2 D h2) (fun i => (h41 i).1.2)
  have hc := canon_ourX L HW R r ρ (e' r ρ) (exc ρ) I h
  refine ⟨ourX L HW R r ρ (e' r ρ) (exc ρ) I, hc, rfl, rfl, rfl, hc.fam.good, ?_, ?_⟩
  · intro hL
    rw [hc.eta]
    have := Nat.floor_le hL
    linarith
  · intro i
    rw [hc.cB]
    exact le_refl _
end GlobalTheory.HubX
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreMore
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
namespace GlobalTheory.StepGlobalPf
variable {D : D7} (i : D.nd.Loc)
variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem main_alt_alt : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.GlobalStatement := by
  intro hA D i r ρ π Xs eρ eχ hr _ _ hG4 hG5 hG5x hG6 hDec _ hS hZ hπ hl hsel hsha
  obtain ⟨S, hS⟩ := hS
  rw [_root_.GlobalTheory.Pass.CutEq.main]
  exact GlobalTheory.CutCore.main hA D i r ρ π Xs eρ eχ S hr hS hZ hπ (noChiOff i r Xs hG6) (unrOut i r ρ π Xs hG4 hDec)
    (atS i r π Xs hG5 hG5x) (atQ i r Xs hG5 hG5x)
    (fun w hw => ⟨(hl w hw).1, (_root_.GlobalTheory.LenModAgree.main.2 D i w hw r Xs _ _ eρ).1 (hl w hw).2.1,
      fun c hc => (_root_.GlobalTheory.LenModAgree.main.2 D i w hw r Xs _ _ eχ).1 ((hl w hw).2.2 c hc)⟩) hsel hsha
end GlobalTheory.StepGlobalPf
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltBisStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_fontaine_at_places_over_l : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i → GoodR D.nd i r → (Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) ∧ (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x)))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) := by
  first | exact @_root_.GlobalTheory.CrysChiOne.main_alt_alt | exact _root_.GlobalTheory.CrysChiOne.main_alt_alt | (intros; apply _root_.GlobalTheory.CrysChiOne.main_alt_alt <;> assumption)
end
end

