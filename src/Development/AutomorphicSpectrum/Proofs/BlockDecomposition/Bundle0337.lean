module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOne
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open GlobalTheory.Parabolic (isIrreducible_of_equiv)

namespace GlobalTheory.CompanionTheory.SegFine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X] {n : ℕ}

abbrev ev (k : Type) [Field k] (n : ℕ) : (∀ _ : Fin 1, GL (Fin n) k) →* GL (Fin n) k :=
  Pi.evalMonoidHom (fun _ : Fin 1 => GL (Fin n) k) 0

abbrev lv (τ : Representation ℂ (GL (Fin n) k) X) : Representation ℂ (∀ _ : Fin 1, GL (Fin n) k) X := τ.comp (ev k n)

theorem stdBlocks_one (h : ∑ _ : Fin 1, n = n) (a : Fin 1) (i : Fin n) :
    stdBlocks (fun _ : Fin 1 => n) h ⟨a, i⟩ = i :=
  Fin.ext (by rw [stdBlocks_val, Subsingleton.elim a 0]; simp)

theorem leviEmb_one (h : ∑ _ : Fin 1, n = n) (g : ∀ _ : Fin 1, GL (Fin n) k) :
    leviEmb k (stdBlocks (fun _ : Fin 1 => n) h) g = g 0 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := leviEmb_apply_same k (stdBlocks (fun _ : Fin 1 => n) h) g 0 i j
  rwa [stdBlocks_one, stdBlocks_one] at this

theorem unipRad_one (h : ∑ _ : Fin 1, n = n) : unipRad k (stdBlocks (fun _ : Fin 1 => n) h) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => Units.ext (Matrix.ext fun i j => ?_)
  have := (mem_unipRad.1 hu).2 0 i j
  rwa [stdBlocks_one, stdBlocks_one] at this

def jacEquiv (h : ∑ _ : Fin 1, n = n) (π : Representation ℂ (GL (Fin n) k) V) :
    (lv π).Equiv (GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin 1 => n) h) π) := by
  have hK : twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1 = ⊥ := by
    rw [unipRad_one]
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain rfl : u = 1 := Subsingleton.elim _ _
    simp
  have hd : ∀ g, deltaHalf k (fun _ : Fin 1 => Fin n) g = 1 := fun g => by
    simp [deltaHalf_apply, modExp, Finset.filter_singleton]
  let f : (lv π).IntertwiningMap (GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin 1 => n) h) π) :=
    ⟨(twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1).mkQ, fun g => LinearMap.ext fun v => by
      show Submodule.Quotient.mk (π (g 0) v) = GlobalTheory.SmGL.jac _ π g (Submodule.Quotient.mk v)
      rw [jac_mk, hd, leviEmb_one]
      simp⟩
  refine equivOfBijective f ⟨(injective_iff_map_eq_zero _).2 fun v hv => ?_, Submodule.Quotient.mk_surjective _⟩
  have : v ∈ twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
  rw [hK] at this
  exact this

def piTensorEquiv (τ : Representation ℂ (GL (Fin n) k) X) :
    (lv τ).Equiv (piTensor fun _ : Fin 1 => τ) := by
  let L := (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => X) 0).symm
  have hL : ∀ v, L v = PiTensorProduct.tprod ℂ fun _ => v := fun v => by
    rw [LinearEquiv.symm_apply_eq]
    simp
  let f : (lv τ).IntertwiningMap (piTensor fun _ : Fin 1 => τ) :=
    ⟨L.toLinearMap, fun g => LinearMap.ext fun v => by
      show L (τ (g 0) v) = piTensor (fun _ : Fin 1 => τ) g (L v)
      rw [hL, hL, piTensor_tprod]
      exact congrArg _ (funext fun a => by rw [Subsingleton.elim a 0])⟩
  exact equivOfBijective f L.bijective

def subrepComp (τ : Representation ℂ (GL (Fin n) k) X) :
    Subrepresentation (lv τ) ≃o Subrepresentation τ where
  toFun S := ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (fun _ => g) hv⟩
  invFun S := ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (g 0) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp {τ : Representation ℂ (GL (Fin n) k) X} (h : τ.IsIrreducible) :
    (lv τ).IsIrreducible := (subrepComp τ).isSimpleOrder_iff.2 h

theorem jhMult_one (h : ∑ _ : Fin 1, n = n) (τ : Representation ℂ (GL (Fin n) k) X)
    (π : Representation ℂ (GL (Fin n) k) V) :
    jhMult (piTensor fun _ : Fin 1 => τ) (GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin 1 => n) h) π) =
      jhMult (lv τ) (lv π) := by
  rw [← jhMult_congr_left (piTensorEquiv τ), ← jhMult_congr_right _ (jacEquiv h π)]

theorem jm_eq_one (x : IrrGL (k := k)) (π : Representation ℂ (GL (Fin x.1) k) V) (φ : π.Equiv x.rep)
    (y : Fin 1 → IrrGL (k := k)) (hy : ∑ a, (y a).1 = x.1) (hyx : y = fun _ => x) : jm y hy π = 1 := by
  subst hyx
  refine (jhMult_one hy x.rep π).trans ?_
  rw [jhMult_congr_right _ (compEquiv φ (ev k x.1))]
  exact jhMult_self (isIrreducible_comp x.2.rep.irr)

theorem eq_of_one_le_jm (x : IrrGL (k := k)) (π : Representation ℂ (GL (Fin x.1) k) V) (φ : π.Equiv x.rep)
    (y : Fin 1 → IrrGL (k := k)) (hy : ∑ a, (y a).1 = x.1) (h : 1 ≤ jm y hy π) : y 0 = x := by
  obtain ⟨z, rfl⟩ : ∃ z, y = fun _ => z := ⟨y 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  obtain ⟨d, c⟩ := z
  obtain ⟨m, b⟩ := x
  obtain rfl : d = m := by simpa using hy
  have h0 : jhMult (lv c.rep.ρ) (lv π) ≠ 0 := by
    rw [← jhMult_one hy]
    exact ENat.one_le_iff_ne_zero.1 h
  have hπ : π.IsIrreducible := isIrreducible_of_equiv φ.symm b.rep.irr
  obtain ⟨E⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv (isIrreducible_comp c.rep.irr) (isIrreducible_comp hπ)
  let f : π.IntertwiningMap c.rep.ρ := ⟨E.toLinearEquiv.toLinearMap, fun g => LinearMap.ext fun v =>
    E.toIntertwiningMap.isIntertwining _ _ (fun _ => g) v⟩
  have E' : c.rep.ρ.Equiv b.rep.ρ := (equivOfBijective f E.toLinearEquiv.bijective).symm.trans φ
  exact congrArg (Sigma.mk d) (irrCl_eq_iff.2 ⟨E'⟩)

theorem dec_single (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) : dec (Segment.single ρ hρ) = fun _ => ρ := funext fun a => by
  show ρ.nu (((Fin.rev (a : Fin 1) : Fin 1) : ℕ) : ℂ) = ρ
  simp [Fin.val_eq_zero]

theorem not_one_le_jm {N c : ℕ} {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsCuspidal π)
    (y : Fin (c + 2) → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) (hc : ∀ a, (y a).IsCusp) : ¬ 1 ≤ jm y hy π := by
  intro h
  have hne : unipRad k (stdBlocks (fun a => (y a).1) hy) ≠ ⊥ := CuspMax.unipRad_ne_bot_iff.2
    ⟨stdBlocks (fun a => (y a).1) hy ⟨0, ⟨0, (hc 0).1⟩⟩, stdBlocks (fun a => (y a).1) hy ⟨1, ⟨0, (hc 1).1⟩⟩, by simp⟩
  have := hπ.2 _ _ _ hne
  have hn : Nontrivial (PiTensorProduct ℂ fun a => (y a).2.rep.V) :=
    GlobalTheory.ProdSupport.nontrivial_piTensor _ fun a => Model.nontrivial_of_isIrreducible (y a).2.rep.irr
  obtain ⟨S, f, hf⟩ := jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h)
  exact not_subsingleton _ hf.subsingleton

theorem fineJac_one (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h : Δ.len = 1) : FineJac Δ := by
  obtain ⟨ρ, hρ, rfl⟩ : ∃ ρ hρ, Δ = Segment.single ρ hρ :=
    ⟨Δ.first, Δ.isCusp_first, Segment.ext_first rfl h⟩
  intro N V _ _ π hπ
  obtain rfl : ρ.1 = N := by
    have := hπ.deg_eq
    simpa [Segment.deg, Segment.single, Segment.ofFirst] using this
  obtain ⟨φ⟩ := (single_spec hρ).2.1.unique hπ
  refine ⟨fun hd => jm_eq_one ρ π φ _ hd (dec_single ρ hρ), fun c y hy hc h1 => ?_⟩
  rcases c with _ | _ | c
  · exact absurd hy (by simpa using hρ.1.ne)
  · have key : ∀ (z : Fin 1 → IrrGL (k := k)) (hz : ∑ a, (z a).1 = ρ.1), 1 ≤ jm z hz π →
        ∀ a, z a = ρ := fun z hz h1 a => by
      rw [Subsingleton.elim a 0]
      exact eq_of_one_le_jm ρ π φ z hz h1
    exact ⟨rfl, fun a => (key y hy h1 a).trans (congrFun (dec_single ρ hρ) _).symm⟩
  · exact absurd h1 (not_one_le_jm (isCuspidal_of_equiv φ.symm hρ.2) y hy hc)

end GlobalTheory.CompanionTheory.SegFine

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimCoefficientsFiniteDetermining
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.UniSol

theorem exists_finset_separating {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ S : Finset K, ∀ c ∈ A, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  classical
  have key : ∀ (n : ℕ) (B : Submodule ℂ A), Module.finrank ℂ B = n →
      ∃ S : Finset K, ∀ c ∈ B, (∀ κ ∈ S, (c : K → ℂ) κ = 0) → c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro B hB
      by_cases hbot : B = ⊥
      · refine ⟨∅, fun c hc _ => ?_⟩
        rw [hbot] at hc
        exact (Submodule.mem_bot ℂ).mp hc
      · obtain ⟨c0, hc0B, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
        obtain ⟨κ0, hκ0⟩ : ∃ κ0, (c0 : K → ℂ) κ0 ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hc0 (Subtype.ext (funext hcon))
        let ev : A →ₗ[ℂ] ℂ := (LinearMap.proj κ0).comp A.subtype
        let B' : Submodule ℂ A := B ⊓ LinearMap.ker ev
        have hlt : B' < B := by
          refine lt_of_le_of_ne inf_le_left (fun h => hκ0 ?_)
          have hmem : c0 ∈ B' := by
            rw [h]
            exact hc0B
          exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2
        have hrk : Module.finrank ℂ B' < n := by
          have := Submodule.finrank_lt_finrank_of_lt hlt
          omega
        obtain ⟨S', hS'⟩ := ih _ hrk B' rfl
        refine ⟨insert κ0 S', fun c hc hvan => hS' c ?_ (fun κ hκ => hvan κ (Finset.mem_insert_of_mem hκ))⟩
        refine Submodule.mem_inf.mpr ⟨hc, LinearMap.mem_ker.mpr ?_⟩
        exact hvan κ0 (Finset.mem_insert_self κ0 S')
  obtain ⟨S, hS⟩ := key _ ⊤ rfl
  refine ⟨S, fun c hc hvan => ?_⟩
  have h0 := hS ⟨c, hc⟩ Submodule.mem_top hvan
  exact congrArg Subtype.val h0

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let m : (Module.Free.ChooseBasisIndex ℂ W) × (Module.Free.ChooseBasisIndex ℂ W) → (K → ℂ) :=
    fun ij k => b.repr (ρ k (b ij.2)) ij.1
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range m)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range m)
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ Submodule.span ℂ (Set.range m) := by
    unfold GlobalTheory.Published.AutFin.coeffSpan
    refine Submodule.span_le.mpr ?_
    rintro f ⟨ℓ, w, rfl⟩
    have hw : ∀ v : W, ℓ v = ∑ i, b.repr v i * ℓ (b i) := by
      intro v
      conv_lhs => rw [← b.sum_repr v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul]
    have hf : (fun k => ℓ ((ρ k) w)) = ∑ ij, (b.repr w ij.2 * ℓ (b ij.1)) • m ij := by
      funext k
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, m]
      rw [Fintype.sum_prod_type]
      dsimp only
      have h1 : ℓ (ρ k w) = ∑ j, b.repr w j * ℓ (ρ k (b j)) := by
        conv_lhs => rw [← b.sum_repr w]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, smul_eq_mul]
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hw (ρ k (b j)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hf]
    exact Submodule.sum_mem _ (fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle

theorem coeffSpan_unisolvent : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W), ∃ S : Finset K, ∀ c ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  intro K W _ _ _ _ ρ
  haveI := finiteDimensional_coeffSpan ρ
  exact exists_finset_separating _

end GlobalTheory.CompanionTheory.CTFin.UniSol

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthExistsCoatom
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.FiniteLengthQuot

theorem exists_isCoatom_subrepresentation :
    ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
      HasFiniteLength ρ → Nontrivial V → ∃ S : Subrepresentation ρ, IsCoatom S := by
  intro G V _ _ _ ρ hfl hnt
  have : WellFoundedGT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hfl).1
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨M, hM, -⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  exact ⟨M, hM⟩

end GlobalTheory.CompanionTheory.FiniteLengthQuot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest
section
noncomputable section

open NumberField IsDedekindDomain Matrix Topology Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.KerTwFin

section Rational

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem discreteTopology_range : DiscreteTopology (ratGL E n).range :=
  GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E n

theorem isClosed_range : IsClosed ((ratGL E n).range : Set (GA E n)) :=
  GroundTheory.Automorphic.AdelicGLn.isClosed_rationalGL E n

theorem injective_ratGL : Function.Injective (ratGL E n) :=
  GroundTheory.Automorphic.AdelicGLn.diagonal_injective E n

theorem finite_ratGL_mem {K : Set (GA E n)} (hK : IsCompact K) : {d : GL (Fin n) E | ratGL E n d ∈ K}.Finite := by
  have hcomp : IsCompact (K ∩ ((ratGL E n).range : Set (GA E n))) := hK.inter_right isClosed_range
  have hdisc : DiscreteTopology ↥(K ∩ ((ratGL E n).range : Set (GA E n))) :=
    DiscreteTopology.of_subset (s := ((ratGL E n).range : Set (GA E n))) discreteTopology_range inter_subset_right
  have hfin := hcomp.finite ⟨hdisc⟩
  refine (hfin.preimage (f := ratGL E n) injective_ratGL.injOn).subset fun d hd => ?_
  exact ⟨hd, d, rfl⟩

end Rational

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_thetaA : Continuous (thetaA E n) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h0 : Continuous fun g : GA E n => ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) :=
      Units.continuous_coe_inv
    exact (h0.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose
  · have h0 : Continuous fun g : GA E n => (g : Matrix (Fin n) (Fin n) (Ad E)) := Units.continuous_val
    exact (h0.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose

theorem finite_kernel {φ : GA E n → ℂ} (hφ : HasCompactSupport φ) {C C' : Set (GA E n)} (hC : IsCompact C)
    (hC' : IsCompact C') :
    {d : GL (Fin n) E | ∃ x ∈ C, ∃ y ∈ C', φ (x⁻¹ * ratGL E n d * thetaA E n y) ≠ 0}.Finite := by
  have hK : IsCompact (C * tsupport φ * (thetaA E n '' C')⁻¹) :=
    (hC.mul hφ).mul (hC'.image continuous_thetaA).inv
  refine (finite_ratGL_mem hK).subset ?_
  rintro d ⟨x, hx, y, hy, h⟩
  have hd : ratGL E n d =
      x * (x⁻¹ * ratGL E n d * thetaA E n y) * (thetaA E n y)⁻¹ := by group
  change ratGL E n d ∈ C * tsupport φ * (thetaA E n '' C')⁻¹
  rw [hd]
  exact Set.mul_mem_mul (Set.mul_mem_mul hx (subset_tsupport _ h))
    (Set.inv_mem_inv.2 (mem_image_of_mem _ hy))

theorem finite_twConj {φ : GA E n → ℂ} (hφ : HasCompactSupport φ) {C : Set (GA E n)} (hC : IsCompact C) :
    {d : GL (Fin n) E | ∃ x ∈ C, φ (twConj (thetaA E n) x (ratGL E n d)) ≠ 0}.Finite :=
  (finite_kernel hφ hC hC).subset fun _ ⟨x, hx, h⟩ => ⟨x, hx, x, hx, h⟩

theorem finite_twConj_of_isTest {φ : GA E n → ℂ} (hφ : IsTest φ) {C : Set (GA E n)} (hC : IsCompact C) :
    {d : GL (Fin n) E | ∃ x ∈ C, φ (twConj (thetaA E n) x (ratGL E n d)) ≠ 0}.Finite :=
  finite_twConj hφ.supp hC

theorem kerFin : PositivityTheory.Rg.BcB.D4.KerFin := fun _ _ _ _ _ _ hφ _ hC => finite_twConj_of_isTest hφ hC

end GlobalTheory.CompanionTheory.KerTwFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeEigenFinite
section
namespace GlobalTheory.CompanionTheory.HeckeEnd

open PositivityTheory.Rg.BcB.F.Tail.PExp

theorem hkE_fin : HkEFin := by
  intro G V _ _ _ ρ K f hf v
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkE PositivityTheory.Rg.BcB.F.Tail.PExp.hkS
  rw [finsum_eq_sum_of_support_subset (s := hf.toFinset),
    finsum_eq_sum_of_support_subset (s := hf.toFinset), LinearMap.sum_apply]
  · rfl
  all_goals
    intro q hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    rw [Function.mem_support] at hq
    exact hq (by simp [h])

end GlobalTheory.CompanionTheory.HeckeEnd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.JmMono

section General

variable {F G U V W : Type} [Field F] [Group G] [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem occursTimes_of_isSubquotient {σ : Representation F G U} {π : Representation F G V}
    {P : Representation F G W} (h : IsSubquotient π P) {r : ℕ} (ho : OccursTimes σ π r) :
    OccursTimes σ P r := by
  obtain ⟨S, f, hf⟩ := h
  unfold GlobalTheory.SmGL.OccursTimes at ho ⊢
  obtain ⟨A, B, hBA, hAB, hiso⟩ := ho
  let ι : Representation.IntertwiningMap S.toRepresentation P :=
    ⟨S.toSubmodule.subtype, fun _ => LinearMap.ext fun _ => rfl⟩
  have hι : Function.Injective ι := fun a b hab => Subtype.val_injective hab
  refine ⟨fun i => GlobalTheory.JHMult.subMap ι (GlobalTheory.JHMult.subComap f (A i)),
    fun i => GlobalTheory.JHMult.subMap ι (GlobalTheory.JHMult.subComap f (B i)),
    fun i => GlobalTheory.JHMult.subMap_mono ι (GlobalTheory.JHMult.subComap_mono f (hBA i)),
    fun i j hij => GlobalTheory.JHMult.subMap_mono ι (GlobalTheory.JHMult.subComap_mono f (hAB i j hij)),
    fun i => ?_⟩
  exact GlobalTheory.JHMult.step_iff.mpr
    (GlobalTheory.JHMult.step_map ι hι
      (GlobalTheory.JHMult.step_comap f hf
        (GlobalTheory.JHMult.step_iff.mp (hiso i))))

theorem jhMult_le_of_isSubquotient (σ : Representation F G U) {π : Representation F G V}
    {P : Representation F G W} (h : IsSubquotient π P) : jhMult σ π ≤ jhMult σ P := by
  unfold GlobalTheory.SmGL.jhMult
  exact iSup₂_le fun r hr => le_iSup₂_of_le r (GlobalTheory.CompanionTheory.JmMono.occursTimes_of_isSubquotient h hr) le_rfl

end General

theorem jm_le_of_isSubquotient {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (y : Fin h → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V)
    (P : Representation ℂ (GL (Fin N) k) W) (hP : IsSmooth P) (h : IsSubquotient π P) :
    jm y hy π ≤ jm y hy P := by
  unfold Zc.jm
  exact GlobalTheory.CompanionTheory.JmMono.jhMult_le_of_isSubquotient _
    (GlobalTheory.JacquetExact.isSubquotient_jac _ hP h)

end GlobalTheory.CompanionTheory.JmMono

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSingleSegmentIsSegmentRep
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.LocGL

theorem isLSeg_of_isL_singleton : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsL {Δ} π → IsLSeg Δ π := by
  intro k _ _ _ _ Δ N V _ _ π h
  obtain ⟨h', x, hd, ⟨Δ', ⟨hm, -⟩, hL⟩, hc⟩ := h
  have hcard : h' = 1 := by
    have := congrArg Multiset.card hm
    simpa using this
  subst hcard
  have hΔ : Δ' 0 = Δ := by
    have hmem : Δ' 0 ∈ Finset.univ.val.map Δ' := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
    rw [hm] at hmem
    simpa using hmem
  have hL0 : IsLSeg Δ (x 0).rep := hΔ ▸ hL 0
  obtain ⟨y, rfl⟩ : ∃ y, x = fun _ => y := ⟨x 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hN : y.1 = N := by simpa using hd
  subst hN
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one y hd
  obtain ⟨φ⟩ := hc.unique ((isCosocle_self y.2.rep.irr).of_equiv (.refl _) ψ)
  exact hL0.of_equiv φ

end GlobalTheory.CompanionTheory.LocGL
end

