module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftDefiniteFormsEqUnitaryFormsClassSumPairing
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.LiftForms

theorem exists_embed {K N W : Type} [Field K] [AddCommGroup N] [Module ℂ N] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {σ : K →+* ℂ} {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (li : LinearIndependent ℂ (fun k => j (Pi.single k 1)))
    (sp : Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤) (a : (Fin n → K) → N)
    (hadd : ∀ x y, a (x + y) = a x + a y) (hsmul : ∀ (c : K) x, a (c • x) = σ c • a x)
    (C : Submodule ℂ N) (ip : N → N → ℂ) (hC : PeterssonHilbertSpace.IsHermPos C ip) (hsp : Submodule.span ℂ (Set.range a) = C)
    (hip : ∀ x x', ⟪j x, j x'⟫_ℂ = ip (a x) (a x')) :
    ∃ J : W →ₗ[ℂ] N, Function.Injective J ∧ LinearMap.range J = C ∧ (∀ x x', ⟪x, x'⟫_ℂ = ip (J x) (J x')) ∧
      ∀ x, J (j x) = a x := by
  classical
  let b : Module.Basis (Fin n) ℂ W := Module.Basis.mk li sp.ge
  have hb : ∀ k, b k = j (Pi.single k 1) := fun k => Module.Basis.mk_apply li sp.ge k
  let J : W →ₗ[ℂ] N := b.constr ℂ fun k => a (Pi.single k 1)
  let a' : (Fin n → K) →ₛₗ[σ] N := { toFun := a, map_add' := hadd, map_smul' := hsmul }
  have hJ : ∀ x, J (j x) = a x := by
    have h : (J : W →ₛₗ[RingHom.id ℂ] N).comp j = a' := by
      refine (Pi.basisFun K (Fin n)).ext fun k => ?_
      rw [Pi.basisFun_apply, LinearMap.comp_apply, ← hb]
      exact b.constr_basis ℂ _ k
    intro x
    exact LinearMap.congr_fun h x
  have htop : ∀ u : W, u ∈ Submodule.span ℂ (Set.range j) := by
    intro u
    have hu : u ∈ Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) := sp ▸ Submodule.mem_top
    exact Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩) hu
  have hr : LinearMap.range J = C := by
    have h1 : Submodule.span ℂ (Set.range j) = ⊤ := eq_top_iff.2 fun u _ => htop u
    rw [LinearMap.range_eq_map, ← h1, Submodule.map_span, ← Set.range_comp, ← hsp]
    congr 2
    exact funext hJ
  have hm : ∀ u, J u ∈ C := fun u => hr ▸ LinearMap.mem_range_self J u
  have hz : ∀ v, ip 0 (J v) = 0 := by
    intro v
    have := hC.smul 0 0 ⟨_, hm v⟩
    simpa using this
  have left : ∀ v, (∀ x, ⟪j x, v⟫_ℂ = ip (J (j x)) (J v)) → ∀ u, ⟪u, v⟫_ℂ = ip (J u) (J v) := by
    intro v hv u
    induction htop u using Submodule.span_induction with
    | mem _ h => obtain ⟨x, rfl⟩ := h; exact hv x
    | zero => rw [inner_zero_left, map_zero, hz]
    | add p q _ _ hp hq =>
      rw [inner_add_left, map_add (f := _), hp, hq]
      exact (hC.add ⟨_, hm p⟩ ⟨_, hm q⟩ ⟨_, hm v⟩).symm
    | smul s p _ hp =>
      rw [inner_smul_left, map_smul, hp]
      exact (hC.smul s ⟨_, hm p⟩ ⟨_, hm v⟩).symm
  have hall : ∀ u v, ⟪u, v⟫_ℂ = ip (J u) (J v) := by
    intro u v
    refine left v (fun x => ?_) u
    have h1 : ⟪v, j x⟫_ℂ = ip (J v) (J (j x)) := left (j x) (fun x' => by rw [hJ, hJ, hip]) v
    rw [← inner_conj_symm, h1]
    exact hC.herm ⟨_, hm v⟩ ⟨_, hm (j x)⟩
  refine ⟨J, ?_, hr, hall, hJ⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro u hu
  have h := hall u u
  rw [show ip (J u) (J u) = ip 0 (J u) by rw [hu], hz] at h
  exact inner_self_eq_zero.1 h


set_option maxHeartbeats 2000000 in
theorem lift_forms_embed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m) (t : T) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 i t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] W), LinearIndependent ℂ (fun k => j (Pi.single k 1)) → Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤ → (∀ x x', ⟪j x, j x'⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A3.A F.lv2.P0 F.lv2.ψ0 i t) x x')) → ∃ J : W →ₗ[ℂ] (GA D ((y.L F.lv2).V i) → (y.L F.lv2).TauV i), Function.Injective J ∧ LinearMap.range J = (y.L F.lv2).Amt (y.tup t) i ∧ (∀ x x', ⟪x, x'⟫_ℂ = (y.L F.lv2).ipA (y.tup t) i (J x) (J x')) ∧ ∀ x, J (j x) = R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ _ hP hH y i t W _ _ j li sp hip
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  have hok : A3.A.fam.Ok 1 := hH.ok.ok2
  have h := (GlobalTheory.T.classSums_eq_pairings_topChain_lifts D G Pl0 T A3.A Ks R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj hB hP.keep.prX hok (y.tup t)).2.2 i
  have hA := GlobalTheory.HilbertLevels.hermA R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj (y.tup t) i
  have key : ∀ t', t' = t → (Submodule.span ℂ (Set.range fun x => R.toRealDat.extV i t' (R.toRealDat.jV i t' (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t' x))) = (y.L F.lv2).Amt (y.tup t) i ∧ ∀ x x', (y.L F.lv2).ipA (y.tup t) i (R.toRealDat.extV i t' (R.toRealDat.jV i t' (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t' x))) (R.toRealDat.extV i t' (R.toRealDat.jV i t' (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t' x'))) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A3.A F.lv2.P0 F.lv2.ψ0 i t') x x')) →
      (Submodule.span ℂ (Set.range fun x => R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x))) = (y.L F.lv2).Amt (y.tup t) i ∧ ∀ x x', (y.L F.lv2).ipA (y.tup t) i (R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x))) (R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x'))) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A3.A F.lv2.P0 F.lv2.ψ0 i t) x x')) := by
    rintro _ rfl h'
    exact h'
  obtain ⟨h1, h2⟩ := key (y.tupT (y.tup t)) (y.tupT_tup t) h
  refine exists_embed j li sp
    (fun x => R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x))) ?_ ?_ _ _ hA h1 ?_
  · intro x x'
    simp only [DatApi.liftForm_add]
    exact (congrArg _ (map_add (R.toRealDat.jV i t) _ _)).trans (map_add (R.toRealDat.extV i t) _ _)
  · intro c x
    simp only [DatApi.liftForm_smul]
    exact (congrArg _ (map_smulₛₗ (R.toRealDat.jV i t) _ _)).trans (map_smul (R.toRealDat.extV i t) _ _)
  · intro x x'
    exact (hip x x').trans (h2 x x').symm

end GlobalTheory.Mem.R3.Rw.LiftForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBridgesAtPlacesOverResidueCharOfLargeCoeff
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.BridgeAll

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

theorem exists_finExt_ge {l : ℕ} [Fact l.Prime] {ι : Type} (S : Set ι) (hS : S.Finite) (L : ι → Loc.FinExt l) :
    ∃ F : Loc.FinExt l, ∀ i ∈ S, (L i).1 ≤ F.1 := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨⟨⊥, inferInstance⟩, fun i hi => absurd hi (Set.notMem_empty i)⟩
  | @insert a s _ _ ih =>
    obtain ⟨F, hF⟩ := ih
    have h1 := F.2
    have h2 := (L a).2
    refine ⟨⟨(L a).1 ⊔ F.1, IntermediateField.finiteDimensional_sup _ _⟩, ?_⟩
    rintro i (rfl | hi)
    · exact le_sup_left
    · exact (hF i hi).trans le_sup_right

theorem placesOver_finite (E : Type) [Field E] [NumberField E] {l : ℕ} (hl : l.Prime) :
    (placesOver E l).Finite := by
  have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem exists_bridge_good {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω]
    [IsAlgClosure H.E Ω] (u : HeightOneSpectrum (𝓞 H.E)) (A : ValuationSubring Ω) (hA : IsPlaceOver A u) :
    ∃ L0 : Loc.FinExt l, u ∈ placesOver H.E l → ∀ LL : Loc.FinExt l, L0.1 ≤ LL.1 →
      ∃ Bw : LocBridge l H.E Ω (Dec (F := H.E) A) ↥(Loc.OL LL),
        (∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1) ∧ Loc.GoodCoef H.condN Bw.LL ∧
        ∀ x : ↥(Loc.OL LL), ((Bw.toLL x : ↥Bw.LL.1) : Loc.Om l) = ((x : ↥LL.1) : Loc.Om l) := by
  by_cases hu : u ∈ placesOver H.E l
  · obtain ⟨j, L0, hj, hB⟩ := GlobalTheory.PlaceBridge.exists_locBridge l H.E Ω u A hu hA
    let L1 : Loc.FinExt l := UpperTheory.KStar.Cyc.rootsExt l _ (UpperTheory.KStar.Cyc.lcm_ne_zero (l := l) H.toHostRaw)
    have f0 := L0.2
    have f1 := L1.2
    refine ⟨⟨L0.1 ⊔ L1.1, IntermediateField.finiteDimensional_sup _ _⟩, fun _ LL hLL => ?_⟩
    obtain ⟨Bw, e1, e2, e3, e4⟩ := hB LL (le_sup_left.trans hLL)
    refine ⟨Bw, by rw [e1]; exact hj, ?_, e4⟩
    rw [e2]
    exact UpperTheory.KStar.Cyc.mem_of_rootsExt_le _ (le_sup_right.trans hLL)
  · exact ⟨⟨⊥, inferInstance⟩, fun h => absurd h hu⟩

theorem brAt_of_large : ∀ (D : D7) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w),
    ∀ (X : CoefIn D.what₂) (j : ℕ), F0.1 ≤ (X.Kx j w).1 → BrAt X j w := by
  intro D w
  choose L hL using fun u : PlE D.host =>
    exists_bridge_good D.host (D.what₂.places.resChar w) D.nd.Om u (D.nd.plOm.1 u) (D.nd.plOm.2 u)
  obtain ⟨F, hF⟩ := exists_finExt_ge _ (placesOver_finite D.host.E (D.what₂.places.resChar_prime w)) L
  refine ⟨F, fun X j hX u hu => ?_⟩
  obtain ⟨Bw, h1, h2, h3⟩ := hL u hu (X.Kx j w) ((hF u hu).trans hX)
  exact ⟨Bw, h1, h2, fun z => (iqC_alg X j w z).trans (h3 z).symm⟩

end GlobalTheory.HeckeLocN.BridgeAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationGaloisCharacterContinuous
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocCont

open IsLocalRing

theorem continuous_of_le_comap {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (maximalIdeal A)) (hB : IsAdic (maximalIdeal B)) (φ : A →+* B)
    (h : maximalIdeal A ≤ (maximalIdeal B).comap φ) : Continuous φ := by
  apply continuous_of_continuousAt_zero φ.toAddMonoidHom
  rw [isAdic_iff] at hA hB
  intro s hs
  simp only [map_zero] at hs
  obtain ⟨n, hn⟩ := hB.2 s hs
  have h1 : ((maximalIdeal A ^ n : Ideal A) : Set A) ∈ nhds (0 : A) :=
    (hA.1 n).mem_nhds (Ideal.zero_mem _)
  refine Filter.mem_map.2 (Filter.mem_of_superset h1 fun a ha => hn ?_)
  have : (maximalIdeal A ^ n).map φ ≤ maximalIdeal B ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 h) n
  exact this (Ideal.mem_map_of_mem φ ha)

theorem comap_maximalIdeal_padicInt {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] : (maximalIdeal O).comap (algebraMap ℤ_[p] O) = maximalIdeal ℤ_[p] :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal O))

theorem p_mem_maximalIdeal {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] : ((p : ℕ) : O) ∈ maximalIdeal O := by
  have hp : ((p : ℕ) : ℤ_[p]) ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  rw [← comap_maximalIdeal_padicInt O] at hp
  simpa using hp

theorem le_comap_of_padicInt {p : ℕ} [Fact p.Prime] {A B : Type} [CommRing A] [IsLocalRing A] [Algebra ℤ_[p] A]
    [Module.Finite ℤ_[p] A] [CommRing B] [IsLocalRing B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] (φ : A →+* B)
    (hφ : ∀ z, φ (algebraMap ℤ_[p] A z) = algebraMap ℤ_[p] B z) : maximalIdeal A ≤ (maximalIdeal B).comap φ := by
  have hc : ((maximalIdeal B).comap φ).comap (algebraMap ℤ_[p] A) = maximalIdeal ℤ_[p] := by
    rw [Ideal.comap_comap, ← comap_maximalIdeal_padicInt B]
    congr 1
    exact RingHom.ext hφ
  haveI : ((maximalIdeal B).comap φ).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap ℤ_[p] A)
      (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance))
      ((maximalIdeal B).comap φ) (by rw [hc]; infer_instance)
  exact (IsLocalRing.eq_maximalIdeal this).ge

theorem continuous_of_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p = q) {A B : Type} [CommRing A] [IsLocalRing A]
    [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B] [IsLocalRing B]
    [Algebra ℤ_[q] B] [Module.Finite ℤ_[q] B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (maximalIdeal A)) (hB : IsAdic (maximalIdeal B)) (φ : A →+* B)
    (hφ : ∀ (z : ℤ_[p]) (z' : ℤ_[q]), HEq z z' → φ (algebraMap ℤ_[p] A z) = algebraMap ℤ_[q] B z') : Continuous φ := by
  subst hpq
  exact continuous_of_le_comap hA hB φ (le_comap_of_padicInt φ fun z => hφ z z HEq.rfl)

theorem continuous_algebraMap_padicInt {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] [TopologicalSpace O] [IsTopologicalRing O] (hO : IsAdic (maximalIdeal O)) :
    Continuous (algebraMap ℤ_[p] O) := by
  refine continuous_of_continuousAt_zero (algebraMap ℤ_[p] O) ?_
  rw [ContinuousAt, map_zero, hO.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  have hl : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[p]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (p_mem_maximalIdeal O) n)

section Units

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem continuous_units {O : Type} [Monoid O] [TopologicalSpace O] (φ : Γ →* Oˣ)
    (h : Continuous fun g => (φ g : O)) : Continuous φ := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  have : (fun g => ((φ g)⁻¹ : Oˣ).val) = fun g => (φ g⁻¹ : O) := by
    funext g; rw [map_inv]
  rw [this]
  exact h.comp continuous_inv

theorem continuous_unitsMap {A B : Type} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B] (f : A →* B)
    (hf : Continuous f) : Continuous (Units.map f) :=
  Units.continuous_iff.2 ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩

theorem continuous_of_isOpen_ker {N : Type} [Group N] [TopologicalSpace N] (φ : Γ →* N)
    (h : IsOpen (φ.ker : Set Γ)) : Continuous φ := by
  refine IsLocallyConstant.continuous fun s => ?_
  have e : φ ⁻¹' s = ⋃ x ∈ φ ⁻¹' s, (fun g => x⁻¹ * g) ⁻¹' (φ.ker : Set Γ) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_iUnion, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, exists_prop]
    constructor
    · intro hg; exact ⟨g, hg, inv_mul_cancel _⟩
    · rintro ⟨x, hx, hxg⟩
      rw [inv_mul_eq_one] at hxg
      rwa [← hxg]
  rw [e]
  exact isOpen_biUnion fun x _ => h.preimage (continuous_const.mul continuous_id)

end Units

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem chiN_continuous : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (twC : ∀ j w, D.ntw.O0 (C.twI w) →+* OcC X j w) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)) (hP : PsiInt X ψ0), (∀ j w, TwAlgAt C X j w (twC j w)) → (∀ j w, IsOpen ((psN X ψ0 hP j w).ker : Set (G D.host.E D.nd.Om))) → ∀ (i : LocT (base M C hR X hS)) (c : ℕ), Continuous (fun g => ((chiN (base M C hR X hS) C (fun i => twC (jOf _ i) (wOf _ i)) (fun i => psN X ψ0 hP (jOf _ i) (wOf _ i)) i c g : (OOf (base M C hR X hS) i)ˣ) : OOf (base M C hR X hS) i)) := by
  intro D M C hR X hS twC ψ0 hP htw hker i c
  have hadic : ∀ j w, IsAdic (maximalIdeal (OcC X j w)) := oc_adic X
  have htwc : ∀ j w, Continuous (twC j w) := fun j w =>
    continuous_of_heq (C.twI_l w) (D.ntw.twistBaseCoefficientRing_isAdic (C.twI w)) (hadic j w) (twC j w) (htw j w)
  have h1 : Continuous (D.ntw.chi1 (C.twI (wOf (base M C hR X hS) i)) (Fam.NPC.jOf (base M C hR X hS) i)
      (C.sd (wOf (base M C hR X hS) i))) :=
    continuous_units _ (D.ntw.twistCharacterFamily_continuous _ _ _)
  have h2 : Continuous (psN X ψ0 hP (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)) :=
    continuous_of_isOpen_ker _ (hker _ _)
  have h3 : Continuous (Units.map (twC (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)).toMonoidHom) :=
    continuous_unitsMap _ (htwc _ _)
  haveI : Fact (lOf (base M C hR X hS) i).Prime := ⟨D.what₂.places.resChar_prime _⟩
  letI : Algebra ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i) := (base M C hR X hS).algOc _ _
  haveI : Module.Finite ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i) := (base M C hR X hS).finOc _ _
  have h4 : Continuous (Units.map (algebraMap ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i)).toMonoidHom) :=
    continuous_unitsMap _ (continuous_algebraMap_padicInt _ (hadic _ _))
  have h5 := continuous_cycZ D.host.E D.nd.Om (lOf (base M C hR X hS) i)
  refine Units.continuous_val.comp ?_
  change Continuous fun g =>
    ((show (OOf (base M C hR X hS) i)ˣ from (Units.map (twC (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)).toMonoidHom)
      (D.ntw.chi1 (C.twI (wOf (base M C hR X hS) i)) (Fam.NPC.jOf (base M C hR X hS) i) (C.sd (wOf (base M C hR X hS) i)) g)) *
      (show (OOf (base M C hR X hS) i)ˣ from psN X ψ0 hP (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i) g)) *
    (Units.map (algebraMap ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i)).toMonoidHom
      (cycZ D.host.E D.nd.Om (lOf (base M C hR X hS) i) g)) ^ (-((c : ℤ) - 1))
  exact ((h3.comp h1).mul h2).mul ((h4.comp h5).zpow _)

end GlobalTheory.HeckeLocCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationHeckeRingIsLocalRing
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.TLocal

theorem isLocalRing_of_congr {O X : Type} [CommRing O] [IsLocalRing O] [Finite X] [Nonempty X] (T : Subalgebra O (X → O))
    (h : ∀ f ∈ T, ∀ x y, f x - f y ∈ IsLocalRing.maximalIdeal O) : IsLocalRing T := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have key : ∀ f : T, IsUnit ((f : X → O) x) → IsUnit f := by
    intro f hx
    have : Algebra.IsIntegral T (X → O) := Algebra.IsIntegral.tower_top O
    have hu : IsUnit (algebraMap T (X → O) f) := by
      refine Pi.isUnit_iff.2 fun y => ?_
      by_contra hy
      have h1 := add_mem (h f f.2 x y) ((IsLocalRing.mem_maximalIdeal _).2 hy)
      exact (IsLocalRing.mem_maximalIdeal _).1 (by simpa using h1) hx
    have hl := RingHom.IsIntegral.isLocalHom (f := algebraMap T (X → O))
      (fun g => Algebra.IsIntegral.isIntegral g) Subtype.val_injective
    exact hl.map_nonunit f hu
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
  exact (IsLocalRing.isUnit_or_isUnit_one_sub_self ((f : X → O) x)).imp (key f) (key (1 - f))

theorem sub_mem_of_ker_eq {O A : Type} [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A] (ψ φ : A →ₐ[O] O)
    (h : RingHom.ker ((IsLocalRing.residue O).comp ψ.toRingHom) = RingHom.ker ((IsLocalRing.residue O).comp φ.toRingHom))
    (a : A) : ψ a - φ a ∈ IsLocalRing.maximalIdeal O := by
  have h1 : a - algebraMap O A (φ a) ∈ RingHom.ker ((IsLocalRing.residue O).comp φ.toRingHom) := by
    rw [RingHom.mem_ker]; simp
  rw [← h, RingHom.mem_ker] at h1
  rw [← IsLocalRing.residue_eq_zero_iff]
  simpa using h1


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B)
    (i : LocT B), IsLocalRing (TOf B i) := by
  intro R H what₂ B hs hd i
  have := xFin_of hs hd i
  have := xNe_of hs hd i
  refine isLocalRing_of_congr (TOf B i) fun f hf x y => ?_
  rw [← Ideal.Quotient.eq]
  unfold TOf at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨v, k, hvk, rfl⟩ := hf
    refine Ideal.Quotient.eq.2 ?_
    simp only [hTfun, dif_pos hvk]
    exact sub_mem_of_ker_eq x.1 y.1 (x.2.1.trans y.2.1.symm) _
  | algebraMap r => rfl
  | add f g _ _ hf hg => simp only [Pi.add_apply, map_add (f := _), hf, hg]
  | mul f g _ _ hf hg => simp only [Pi.mul_apply, map_mul, hf, hg]

end GlobalTheory.HeckeLocN.TLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmFrameExistsWithJE
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

theorem omFrame_exists_with_jE (D : D7) (jE : D.host.E →+* Qb) : ∃ fr : OmFrame D, fr.jE = jE := by
  letI : Algebra D.host.E Qb := jE.toAlgebra
  haveI : Algebra.IsAlgebraic ℚ Qb := inferInstance
  haveI : IsScalarTower ℚ D.host.E Qb := .of_algebraMap_eq fun x => (map_ratCast jE x).symm
  haveI : Algebra.IsAlgebraic D.host.E Qb := .tower_top (K := ℚ) D.host.E
  haveI : IsAlgClosure D.host.E Qb := ⟨inferInstance, inferInstance⟩
  let e : D.nd.Om ≃ₐ[D.host.E] Qb := IsAlgClosure.equiv D.host.E D.nd.Om Qb
  exact ⟨⟨jE, e.toRingEquiv, fun x => e.commutes x⟩, rfl⟩

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotMeasureEqSmul
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingNorm

theorem sq_eq_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) :
    ((‖x‖ ^ 2 : ℝ) : ℂ) = inner ℂ x x := by
  rw [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K]
  rfl

variable {D : D7}

theorem quotMeasure_eq_smul (V : HSp D) (hs : V.SigOK) {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) : GlobalTheory.AutomorphicL2Unitary.autMeasure V ν = ν 𝓕 • muQ1 V := by
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hp := GlobalTheory.AutomorphicL2Unitary.isVolPair_volPair hP
  have := hp.1.1
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have e := Measure.isMulLeftInvariant_eq_smul ν (volPair V).1
  set c := Measure.haarScalarFactor ν (volPair V).1
  have e1 : GlobalTheory.AutomorphicL2Unitary.autMeasure V ν = (c : ENNReal) • muQ V := by
    rw [GlobalTheory.AutomorphicL2Unitary.muQ_eq hP, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have e2 : ν 𝓕 = c * muQ V Set.univ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]
    exact congrArg (fun m : Measure (AutQ V) => m Set.univ) e1
  rw [e1, e2, muQ1, if_pos (show _ ∧ _ from hV), smul_smul, mul_assoc, ENNReal.mul_inv_cancel hV.1 hV.2, mul_one]

theorem integral_star_mul (V : HSp D) (hs : V.SigOK) {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (φ : GA D V → ℂ) (hφ : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g)
    (ψ : AutQ V → ℂ) (hψ : MemLp ψ 2 (muQ1 V)) (c : ℝ) (h : ∀ q, ‖φ q.out‖ = c * ‖ψ q‖) :
    ∫ g in 𝓕, star (φ g) * φ g ∂ν = (((ν 𝓕).toReal * (c * ‖hψ.toLp ψ‖) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ := hφ
  have e1 := GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕
    (fun q => star (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ q) * GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ q)
  simp only [hL.descend_mk] at e1
  have e2 : ((‖hψ.toLp ψ‖ ^ 2 : ℝ) : ℂ) = ∫ q, ((‖ψ q‖ ^ 2 : ℝ) : ℂ) ∂muQ1 V := by
    rw [sq_eq_inner, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψ.coeFn_toLp] with q hq
    rw [hq, sq_eq_inner]
  rw [← e1, show GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _ from quotMeasure_eq_smul V hs hν h𝓕, integral_smul_measure, mul_pow,
    Complex.ofReal_mul, Complex.ofReal_mul, e2, ← integral_const_mul, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  show star (φ q.out) * φ q.out = ((c ^ 2 : ℝ) : ℂ) * ((‖ψ q‖ ^ 2 : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, ← mul_pow, ← h, Complex.ofReal_pow]
  exact Complex.conj_mul' _

end GlobalTheory.ReadingNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldSplitsInOfIsRayPrimeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassField_splitsIn_of_isRayPrime : ∀ (D : D7) (jE : D.host.E →+* Qb) (M : Fld) (h : KQbar D jE ≤ M) (hf : FiniteDimensional ℚ M),
    letI := GlobalTheory.ParRay.algK D jE h
    haveI := GlobalTheory.ParRay.nfOf hf
    GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host) →
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn M p := by
  first | exact @GlobalTheory.ParRay.rayField_splitsIn_of_isRayPrime | exact GlobalTheory.ParRay.rayField_splitsIn_of_isRayPrime | (intros; apply GlobalTheory.ParRay.rayField_splitsIn_of_isRayPrime <;> assumption)
end

