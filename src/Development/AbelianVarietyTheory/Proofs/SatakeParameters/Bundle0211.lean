module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0164
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanImageMaxGenEigenspace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0146
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0051
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
public import Development.AutomorphicArithmetic.BlochKatoExtensions.PhtCmp
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectorsStatement
section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockLift_action_on_principalCongruenceFixedVectors : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V), u ∈ fixK1 (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) → ∀ (h : GL (Fin r) (ZMod g)) (h' : GL (Fin (r + t)) F), GlobalTheory.PendOf.IsLiftN h h' → ρ h' u = ρ (Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1))) u := by
  first | exact @GlobalTheory.SerSys.BlockLift.blockLift_act | exact GlobalTheory.SerSys.BlockLift.blockLift_act | (intros; apply GlobalTheory.SerSys.BlockLift.blockLift_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CarriedPartEigensystemPassageOfType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.Fwd

theorem sys_of_mem_span {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V)
    (op : I → Module.End K V) (opC : I → Module.End ℂ W)
    (hli : LinearIndependent ℂ (fun k => j (b k))) (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤)
    (hint : ∀ i x, j (op i x) = opC i (j x)) (hc : Formalism.L2.Col.PairComm opC) (Q : (I → K) → Prop) {u : W}
    (hu : u ∈ Submodule.span ℂ (j '' (Formalism.L2.Col.eigSum op Q : Set V))) (hu0 : u ≠ 0) {y : I → ℂ}
    (hy : ∀ i, opC i u = y i • u) : ∃ s, Q s ∧ y = fun i => σ (s i) := by
  have h1 := (GlobalTheory.span_image_eigAt_of_basis σ j b op opC hli hsp hint).2.1 Q
  rw [h1] at hu
  by_contra hne
  have hd := Formalism.L2.Col.disjoint_eigSum hc (C := fun x => ∃ s, Q s ∧ x = fun i => σ (s i)) (C' := fun x => x = y)
    (fun x hx h => hne (h ▸ hx))
  have hu' : u ∈ Formalism.L2.Col.eigSum opC (fun x => x = y) :=
    Formalism.L2.Col.eigAt_le_eigSum (op := opC) (C := fun x => x = y) rfl (Formalism.L2.Col.mem_eigAt_of_forall_apply hy)
  exact hu0 ((Submodule.disjoint_def.1 hd) u hu hu')

end GlobalTheory.Hk3.Fwd


open GlobalTheory.Hk3.Fwd in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Hk3.passage_of_carried : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ p c, R.Carries p c → R.Wc' j c ≠ ⊥ → cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hInt hC hEx hSch hJ s hOk hGen hU hGU hGE hLW hA hPos hB hTr j pl cV cW hLD p c hCar hW
  obtain ⟨sy, x, hxg, hxe, hxW, hx0, hlab⟩ :=
    GlobalTheory.T.exists_good_rational_eigenform_hitting_carried_part hHowe R F hInt hC hEx hSch hJ s hOk hGen hU hGU hGE hLW hA hPos j pl cV cW hLD p c hCar hW
  obtain ⟨hCore, hSF, -, -, hEE, hWW, -⟩ := _root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC
  have core := hCore hEx
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCar.1
  have hu0 := _root_.GlobalTheory.thetaUp_injective_on_carried R F hB hPos p c hCar w hw hw0
  obtain ⟨hOpsX, hOpsV⟩ := GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 core.lev core.fam core.models
  obtain ⟨hX, hXo, hXn⟩ := hOpsX A3.A.μ0
  obtain ⟨hV, hVo, -⟩ := hOpsV j A3.A.μ0
  obtain ⟨plX, cX, c0, hRD⟩ := GlobalTheory.T.every_rowOperator_is_labelOperator_with_partner hHowe R F hInt hC hEx hSch hJ A3.A.μ0
  have hsplit := GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 core.lev core.fam core.models
  have hM := core.models
  have hBx := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.R A3.A.μ0).pres
  obtain ⟨hinj, hrange, -⟩ := hM.HX A3.A.μ0
  have hk := kForm_semi (R.jX A3.A.μ0) (R.HX A3.A.μ0).e (R.B.R A3.A.μ0).pres.extL (fun x => hM.jX A3.A.μ0 x) hinj
    (hrange.trans hBx.2.symm) (Formalism.L2.DIV.CSD.basis _) (Module.Basis.ofVectorSpace _ _) hBx.1
  have hjop : ∀ i f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = hX (plX i) (cX i) (R.jX A3.A.μ0 f) := hRD.op hX hXo
  have hcomm : Formalism.L2.Col.PairComm (fun i => hX (plX i) (cX i)) := fun a b => hXn.1 _ _ (hRD.good a) (hRD.good b) _ _
  have hwE : w ∈ EEc R.toRealDat R.SF c := hEE c ▸ hw
  have hy : ∀ i, hX (plX i) (cX i) (LinearMap.adjoint (R.Th A3.A.μ0) w) =
      evC (Yc D 0) (plX i) (fun d => c (plX i) (dualLab d)) (c0 i) • LinearMap.adjoint (R.Th A3.A.μ0) w := fun i =>
    (_root_.GlobalTheory.Hk3.SysE.matched_commute R.toRealDat F.lv2 core hSch R.SF hSF A3.A.μ0 (plX i) (hRD.good i) (cX i) (c0 i) (hRD.mat i) hX hXo).2 c w hwE
  have hu : LinearMap.adjoint (R.Th A3.A.μ0) w ∈ Submodule.span ℂ (R.jX A3.A.μ0 ''
      (Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll ((A3.rowI A3.A.μ0).HasRes3 p.1) : Set (A3.A.fam.R A3.A.μ0).S.Forms)) :=
    hCar.2 (Submodule.mem_map_of_mem hw)
  obtain ⟨sR, hsR, hyR⟩ := sys_of_mem_span D.what₂.embLL (R.jX A3.A.μ0) (Module.Basis.ofVectorSpace _ _)
    (A3.rowI A3.A.μ0).opAll (fun i => hX (plX i) (cX i)) hk.1 hk.2 hjop hcomm _ hu hu0 hy
  have hXs : ∀ (P : A3.A.ok A3.A.μ0) k, k ≤ D.sp.X'.rank →
      hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (LinearMap.adjoint (R.Th A3.A.μ0) w) =
        D.what₂.embLL (sR (Sum.inl (P, k))) • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    intro P k hkr
    have heq : hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) = hX (plX (Sum.inl (P, k))) (cX (Sum.inl (P, k))) := by
      refine LinearMap.ext_on hk.2 ?_
      rintro _ ⟨b, rfl⟩
      exact ((hsplit.1 A3.A.μ0 hX hXo P k hkr _).symm).trans (hjop (Sum.inl (P, k)) _)
    exact (LinearMap.congr_fun heq _).trans ((hy (Sum.inl (P, k))).trans
      (congrArg (fun z : ℂ => z • LinearMap.adjoint (R.Th A3.A.μ0) w) (congrFun hyR (Sum.inl (P, k)))))
  have hVs : ∀ (P : A3.A.ok A3.A.μ0) k, k ≤ (Vc D j).rank →
      hV (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1) (R.jV j A3.A.μ0 x) =
        D.what₂.embLL (sy (Sum.inl (P, k))) • R.jV j A3.A.μ0 x := by
    intro P k hkr
    have h1 : A3.A.heckeL j A3.A.μ0 (P, k) x = sy (Sum.inl (P, k)) • x := hxe (Sum.inl (P, k))
    exact (hsplit.2 j A3.A.μ0 hV hVo P k hkr x).symm.trans
      ((congrArg (R.jV j A3.A.μ0) h1).trans ((R.jV j A3.A.μ0).map_smulₛₗ _ x))
  have hL := GlobalTheory.T.liftSplitHeckePolys_eq_transfer_residualPolys R.toRealDat F.lv2 hInt core hSch hOk.ok2.irr R.SF hSF j c p.1.1 (fun i => sR (Sum.inl i))
    (fun i => sy (Sum.inl i)) hsR.1 hX hV hXo hVo w hwE hu0 hXs (R.jV j A3.A.μ0 x) (hWW j c ▸ hxW) hx0 hVs
  exact ⟨sy, ⟨hL, hTr j p c hCar sy ⟨x, hxg, hxe, hxW, hx0⟩⟩, hlab⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecomposeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_element_decompose : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ) (c : GAf L n), NG.Cong L n N c → ∃ a b : GAf L n, c = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
  first | exact @GlobalTheory.CongSplit.decomp | exact GlobalTheory.CongSplit.decomp | (intros; apply GlobalTheory.CongSplit.decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamAndJumpsRankOneLAdicCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.TripleGal GlobalTheory.Pst

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_jumps_of_continuous_lAdic_char :
    ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (W : GlobalTheory.HeightCounting.WDSide D T)
      (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (μ : G D.host.E D.nd.Om →* (Qbar l)ˣ),
    Continuous μ → ∀ (J : (D.host.E →+* Qbar l) → Multiset ℤ) (w : HeightOneSpectrum (𝓞 D.host.E)),
    w ∈ placesOver D.host.E l →
    (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw →
      IsdRAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) ∧
      ∀ (τ : D.host.E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ (J τ)) →
    W.IsdRW l ι (rk1 μ) w ∧ ∀ τ : D.host.E →+* Qbar l,
      (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) → W.jumpsW l ι (rk1 μ) τ = J τ :=
  @GlobalTheory.CharAboveRead.deRham_and_jumps_rankOne_lAdic_character
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryRationalHeckeCommuteComplexAutomo
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.EigenConj

theorem opOf_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ) (t : UA E n →₀ ℂ), (∀ g ∈ t.support, g ∈ finU (E := E) (n := n) ∧ ∃ q : ℚ, t g = q) → ∀ (φ φ' : UA E n → ℂ) (z : ℂ), IsAutFormU φ → IsAutFormU φ' → (∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g)) → opOf (RU E n) t φ = z • φ → opOf (RU E n) t φ' = σ z • φ' := by
  intro E _ _ _ n σ t ht φ φ' z hφ hφ' hfin heig
  have key : ∀ (f : UA E n → ℂ) (x : UA E n),
      opOf (RU E n) t f x = ∑ g ∈ t.support, t g * f (x * g) := by
    intro f x
    simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hc1 : Continuous (opOf (RU E n) t φ') := by
    have e : opOf (RU E n) t φ' = fun x => ∑ g ∈ t.support, t g * φ' (x * g) := funext (key φ')
    rw [e]
    exact continuous_finsetSum _ fun g _ =>
      continuous_const.mul (hφ'.cont.comp (continuous_id.mul continuous_const))
  have hc2 : Continuous (σ z • φ') := hφ'.cont.const_smul _
  have hl1 : ∀ γ ∈ ratU E n, ∀ x, opOf (RU E n) t φ' (γ * x) = opOf (RU E n) t φ' x := by
    intro γ hγ x
    rw [key, key]
    simp_rw [mul_assoc, hφ'.left γ hγ]
  have hl2 : ∀ γ ∈ ratU E n, ∀ x, (σ z • φ') (γ * x) = (σ z • φ') x := by
    intro γ hγ x
    simp only [Pi.smul_apply, hφ'.left γ hγ]
  have hfinEq : ∀ h ∈ finU (E := E) (n := n), opOf (RU E n) t φ' h = (σ z • φ') h := by
    intro h hh
    have e := congrFun heig h
    rw [key, Pi.smul_apply, smul_eq_mul] at e
    rw [key, Pi.smul_apply, smul_eq_mul]
    calc ∑ g ∈ t.support, t g * φ' (h * g) = ∑ g ∈ t.support, σ (t g * φ (h * g)) :=
          Finset.sum_congr rfl fun g hg => by
            obtain ⟨hgU, q, hq⟩ := ht g hg
            rw [map_mul, hfin _ ((finU (E := E) (n := n)).mul_mem hh hgU), hq, map_ratCast]
      _ = σ (∑ g ∈ t.support, t g * φ (h * g)) := (map_sum σ _ _).symm
      _ = σ (z * φ h) := by rw [e]
      _ = σ z * φ' h := by rw [map_mul, hfin h hh]
  have hon : Set.EqOn (opOf (RU E n) t φ') (σ z • φ') ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) := by
    rintro _ ⟨γ, hγ, g, hg, rfl⟩
    rw [hl1 γ hγ, hl2 γ hγ]
    exact hfinEq g hg
  exact Continuous.ext_on (GlobalTheory.UnitarySplit.dense_and_split E n).1 hc1 hc2 hon

end GlobalTheory.EigenConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPeriodOfLocalGlobal
section
noncomputable section

namespace GlobalTheory.TameEig

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology

theorem val_apply_eq {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
    (σ : G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (y : Ω) :
    A.valuation (σ y) = A.valuation y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h1 : A.valuation (σ y / y) = 1 := by
      have h2 := Valuation.map_add_eq_of_lt_left A.valuation (x := (1 : Ω)) (y := σ y / y - 1)
        (by rw [map_one]; exact hσ y hy)
      have e : (1 : Ω) + (σ y / y - 1) = σ y / y := by ring
      rwa [e, map_one] at h2
    have hv : A.valuation y ≠ 0 := by simpa using hy
    rw [map_div₀, div_eq_one_iff_eq hv] at h1
    exact h1

theorem wild_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
    (σ : G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  have hv := val_apply_eq A σ hσ
  have hD : σ ∈ Dec (F := E) A := by
    rw [mem_Dec]
    ext x
    have e : x = σ • ((σ⁻¹ : G E Ω) • x) := (smul_inv_smul σ x).symm
    rw [e, ValuationSubring.smul_mem_pointwise_smul_iff, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, AlgEquiv.smul_def σ, hv]
  refine ⟨hD, fun x hx => ?_⟩
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · have e : σ x - x = x * (σ x / x - 1) := by field_simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) (hσ x h0)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem residue_eq_one (N : NData R H what₂) (i : N.Loc) {x : N.O i}
    (hx : x - 1 ∈ IsLocalRing.maximalIdeal (N.O i)) : IsLocalRing.residue (N.O i) x = 1 := by
  rw [← sub_eq_zero, ← map_one (IsLocalRing.residue (N.O i)), ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hx

def chiBar (N : NData R H what₂) (i : N.Loc) : G H.E N.Om →* (IsLocalRing.ResidueField (N.O i))ˣ :=
  (Units.map (IsLocalRing.residue (N.O i)).toMonoidHom).comp (N.chi i 1)

theorem chiBar_val (N : NData R H what₂) (i : N.Loc) (g : G H.E N.Om) :
    ((chiBar N i g : (IsLocalRing.ResidueField (N.O i))ˣ) : IsLocalRing.ResidueField (N.O i)) =
      IsLocalRing.residue (N.O i) (chi1 N i g) := rfl

theorem chiBar_open (N : NData R H what₂) (i : N.Loc) : IsOpen ((chiBar N i).ker : Set (G H.E N.Om)) := by
  have hm : IsOpen (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i)) := by
    have := (isAdic_iff.1 (N.O_adic i)).1 1
    rwa [pow_one] at this
  let U1 : Set (G H.E N.Om) :=
    (fun g => ((N.chi i 1 g : (N.O i)ˣ) : N.O i) - 1) ⁻¹' (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i))
  have hU1 : IsOpen U1 := hm.preimage ((N.chi_cont i 1).sub continuous_const)
  have h1 : (1 : G H.E N.Om) ∈ U1 := by
    show ((N.chi i 1 1 : (N.O i)ˣ) : N.O i) - 1 ∈ IsLocalRing.maximalIdeal (N.O i)
    rw [map_one, Units.val_one, sub_self]; exact Ideal.zero_mem _
  have hsub : U1 ⊆ ((chiBar N i).ker : Set (G H.E N.Om)) := by
    intro g hg
    show Units.map (IsLocalRing.residue (N.O i)).toMonoidHom (N.chi i 1 g) = 1
    ext
    exact residue_eq_one N i hg
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU1.mem_nhds h1) hsub)

theorem not_isPrimePow_15 : ¬ IsPrimePow 15 := by
  intro h
  obtain ⟨p, k, hp, -, he⟩ := (isPrimePow_nat_iff 15).1 h
  have h3 : (3:ℕ) ∣ p ^ k := by rw [he]; norm_num
  have h5 : (5:ℕ) ∣ p ^ k := by rw [he]; norm_num
  have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h3)
  have e5 := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5)
  omega

theorem residue_ne_one (N : NData R H what₂) (i : N.Loc)
    (w : PlE H) (hS : w ∈ N.S i) (q : ℕ) (hq : q.Prime) (hq15 : q % 15 = 1) (hw : w ∈ placesOver H.E q)
    (hDel : Nat.card ((Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1)) = 15) :
    IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)) ≠ 1 := by
  intro h1
  haveI : Fact q.Prime := ⟨hq⟩
  have hval : (N.plOm.1 w).valuation (q : N.Om) < 1 := by
    have := ((N.plOm.2 w) ((q : ℕ) : 𝓞 H.E)).2 hw
    simpa using this
  have hcop : Nat.Coprime 15 q :=
    (Nat.gcd_rec 15 q).trans (by simp only [hq15, Nat.gcd_one_left])
  have hpow : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), N.chi i 1 σ ^ 15 = 1 := by
    intro σ hσ
    have h := pow_card_eq_one' (G := (Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1))
      (x := ⟨N.chi i 1 σ, Subgroup.mem_map_of_mem _ hσ⟩)
    rw [hDel] at h
    exact congrArg Subtype.val h
  have hwild : ∀ σ : G H.E N.Om, (∀ y : N.Om, y ≠ 0 → (N.plOm.1 w).valuation (σ y / y - 1) < 1) →
      σ ∈ (chiBar N i).ker := by
    intro σ hσ
    have hI := wild_mem_Ine (N.plOm.1 w) σ hσ
    have h15 : chiBar N i σ ^ 15 = 1 := by
      show (Units.map (IsLocalRing.residue (N.O i)).toMonoidHom) (N.chi i 1 σ) ^ 15 = 1
      rw [← map_pow, hpow σ hI, map_one]
    exact _root_.GlobalTheory.WildChar.main H.E N.Om q (N.plOm.1 w) hval _ (chiBar N i) (chiBar_open N i) σ
      (fun a ha => hσ a ha) 15 (by norm_num) hcop h15
  have hg : N.gam0 i w ∈ (chiBar N i).ker :=
    MonoidHom.mem_ker.2 (Units.ext (by simp only [chiBar_val, h1, Units.val_one]))
  have hTG := N.restN_tameGenerator_generates i w (Or.inl hS)
  have hle : ((Subgroup.closure (insert (N.gam0 i w) {σ : G H.E N.Om | ∀ y : N.Om, y ≠ 0 →
      (N.plOm.1 w).valuation (σ y / y - 1) < 1}) : Subgroup (G H.E N.Om)) : Set (G H.E N.Om)) ⊆
      ((chiBar N i).ker : Set (G H.E N.Om)) :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hg, fun σ hσ => hwild σ hσ⟩)
  have hcl := Subgroup.isClosed_of_isOpen _ (chiBar_open N i)
  have hIne : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), IsLocalRing.residue (N.O i) (chi1 N i σ) = 1 := by
    intro σ hσ
    have h2 : σ ∈ (chiBar N i).ker := closure_minimal hle hcl (hTG.2 hσ)
    rw [← chiBar_val, MonoidHom.mem_ker.1 h2, Units.val_one]
  have : Finite ((Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hDel]; norm_num)
  obtain ⟨g, hgen⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1))
  obtain ⟨σ, hσ, hσg⟩ := Subgroup.mem_map.1 g.2
  have hord : orderOf (g : (N.O i)ˣ) = 15 := by rw [Subgroup.orderOf_coe, hgen, hDel]
  have hprim : IsPrimitiveRoot ((g : (N.O i)ˣ) : N.O i) 15 := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hord]
    exact IsPrimitiveRoot.orderOf _
  apply _root_.GlobalTheory.primitiveRoot_notPrimePow_map_ne_one _ (N.O i) (IsLocalRing.residue (N.O i)) _ 15 (by norm_num) hprim not_isPrimePow_15
  rw [← hσg]
  exact hIne σ hσ

theorem charpoly_red (N : NData R H what₂) {i : N.Loc} (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i)))
    {w : PlE H} {x : N.X i} (hs : Formalism.MainNotions.SumRepresentations.SplitI N r w x) (γ : G H.E N.Om) (hγ : γ ∈ Ine (F := H.E) (N.plOm.1 w)) :
    ((redRep N i (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly =
      (X - 1) ^ R.r * (X - C (IsLocalRing.residue (N.O i) (chi1 N i γ))) ^ R.t := by
  have hK : (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).charpoly).map
      (algebraMap (N.O i) (Kf N i)) =
      ((X - 1) ^ R.r * (X - C (chi1 N i γ)) ^ R.t).map (algebraMap (N.O i) (Kf N i)) := by
    obtain ⟨Pm, hP⟩ := hs
    have h := hP γ hγ
    rw [← Matrix.charpoly_map]
    have e1 : ((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (algebraMap (N.O i) (Kf N i)) =
        ((mapRep (algebraMap (N.O i) (Kf N i)) (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Kf N i)) := rfl
    have h2 := Matrix.charpoly_units_conj' Pm
      ((mapRep (algebraMap (N.O i) (Kf N i)) (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Kf N i))
    rw [← Matrix.coe_units_inv, ← Units.val_mul, ← Units.val_mul, h] at h2
    rw [e1, ← h2]
    have h3 := Formalism.MainNotions.SumRepresentations.diagHom_charpoly (k := Kf N i) R.r R.t
      (Units.map (algebraMap (N.O i) (Kf N i)).toMonoidHom (N.chi i 1 γ))
    rw [Formalism.MainNotions.SumRepresentations.diagHom_coe] at h3
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_C]
    exact h3
  have hO := Polynomial.map_injective _ (IsFractionRing.injective (N.O i) (Kf N i)) hK
  have e2 : ((redRep N i (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) =
      ((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (IsLocalRing.residue (N.O i)) := rfl
  rw [e2, Matrix.charpoly_map, hO]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one, Polynomial.map_C]

end GlobalTheory.TameEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCount
section
noncomputable section

namespace GlobalTheory.HtCardProof

open _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N _root_.Formalism.L2 Module

section Local

variable {l m : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {K LL : FinExt l}
  (r : ↥(GK K) →* GL (Fin m) ↥LL.1)


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
include T in
theorem exists_count (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) [FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ)] :
    ∃ M : Multiset ℤ, Multiset.card M = finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ) ∧
      ∀ a, (M.count a : ℤ) = multV (P.PD K) (vrep r) τ a := by
  obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) (vrep r) τ
  obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) (vrep r) τ
  have anti := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_anti (P.PD K) (vrep r) τ
  haveI : ∀ a, FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ a) := fun a =>
    Submodule.finiteDimensional_of_le (inf_le_left : FildR (P.PD K) (vrep r) τ a ≤ DdRE (P.PD K) (vrep r) τ)
  have nn : ∀ a, 0 ≤ multV (P.PD K) (vrep r) τ a := fun a => by
    have := Submodule.finrank_mono (anti (show a ≤ a + 1 by omega))
    unfold multV
    omega
  obtain ⟨lo₁, hl1, hl2⟩ : ∃ lo₁, lo₁ ≤ lo ∧ lo₁ ≤ hi := ⟨min lo hi, min_le_left _ _, min_le_right _ _⟩
  have zero : ∀ a, a ∉ Finset.Ico lo₁ hi → multV (P.PD K) (vrep r) τ a = 0 := fun a ha => by
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at ha
    have e : FildR (P.PD K) (vrep r) τ a = FildR (P.PD K) (vrep r) τ (a + 1) := by
      rcases ha with ha | ha
      · exact (hlo a (by omega)).trans (hlo (a + 1) (by omega)).symm
      · exact (hhi a ha).trans (hhi (a + 1) (by omega)).symm
    unfold multV
    rw [e, sub_self]
  refine ⟨∑ a ∈ Finset.Ico lo₁ hi, Multiset.replicate (multV (P.PD K) (vrep r) τ a).toNat a, ?_, fun b => ?_⟩
  · rw [Multiset.card_sum]
    simp only [Multiset.card_replicate]
    have hs : ∑ a ∈ Finset.Ico lo₁ hi, multV (P.PD K) (vrep r) τ a =
        (finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ lo₁) : ℤ) - finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ hi) :=
      Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV _ _ _ _ _ hl2
    have e1 : finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ lo₁) = finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ) := by
      rw [hlo lo₁ hl1]
    have e2 : finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ hi) = 0 := Submodule.finrank_eq_zero.2 (hhi hi le_rfl)
    rw [e1, e2] at hs
    have : ((∑ a ∈ Finset.Ico lo₁ hi, (multV (P.PD K) (vrep r) τ a).toNat : ℕ) : ℤ) =
        (finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ) : ℤ) := by
      push_cast
      rw [Finset.sum_congr rfl fun a _ => Int.toNat_of_nonneg (nn a), hs]
      simp
    exact_mod_cast this
  · rw [Multiset.count_sum']
    simp only [Multiset.count_replicate]
    rw [Finset.sum_ite_eq']
    by_cases hb : b ∈ Finset.Ico lo₁ hi
    · rw [if_pos hb, Int.toNat_of_nonneg (nn b)]
    · rw [if_neg hb, zero b hb]
      rfl

end Local

theorem htCard : GlobalTheory.HeightCounting.HtCard := GlobalTheory.PhtCompare.phtCmp

end GlobalTheory.HtCardProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterIndependentOfLocalEmbeddingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineParameter_independent_of_localEmbedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Loc.Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r → GlobalTheory.Pst.wdAt P ι Bw h hj r = GlobalTheory.Pst.wdAt P ι Bw' h hj' r := by
  first | exact @GlobalTheory.Pst.BridgeWD.wdAt_bridge_indep | exact GlobalTheory.Pst.BridgeWD.wdAt_bridge_indep | (intros; apply GlobalTheory.Pst.BridgeWD.wdAt_bridge_indep <;> assumption)
end

