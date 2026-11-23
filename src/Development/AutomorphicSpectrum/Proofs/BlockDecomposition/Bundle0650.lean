module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0645
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0565
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0595
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0359
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0332
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0593
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0582
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0605
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordHighestWeightVector
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParthasarathyRaoVaradarajan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0378
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0392
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteWeightsInvariantHom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantExtending
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0387
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0642
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicWeightsCoefficient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitKAOfGen
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairSubGeneric
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.DiagCell

namespace GlobalTheory.CompanionTheory.CuspPairSub

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_singleton_of_sum' {ι A : Type*} [Fintype ι] [DecidableEq ι] {a : A} {t : ι → Multiset A}
    (h : ({a} : Multiset A) = ∑ j, t j) : ∃ j₀, t j₀ = {a} ∧ ∀ j, j ≠ j₀ → t j = 0 := by
  have hc : ∑ j, Multiset.card (t j) = 1 := by
    have := congrArg Multiset.card h
    rw [Multiset.card_sum] at this
    simpa using this.symm
  obtain ⟨j₀, -, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hc.symm ▸ one_ne_zero)
  have hz : ∀ j, j ≠ j₀ → t j = 0 := fun j hj => by
    have h2 := Finset.add_le_sum (s := Finset.univ) (f := fun j => Multiset.card (t j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j₀) (Finset.mem_univ j) (Ne.symm hj)
    simp only [hc] at h2
    exact Multiset.card_eq_zero.1 (by omega)
  refine ⟨j₀, ?_, hz⟩
  rw [h, Finset.sum_eq_single j₀ (fun j _ hj => hz j hj) (by simp)]

theorem eq_of_hasSupport_singleton {y z : IrrGL (k := k)} (h : HasSupport y.rep {z}) : y = z := by
  obtain ⟨r, u, hu, hi, hc, e, hsub⟩ := h
  obtain rfl : r = 1 := by simpa using congrArg Multiset.card hu
  obtain rfl : u = fun _ => z := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hu
  obtain ⟨d, c⟩ := y
  obtain rfl : z.1 = d := by simpa using Fintype.card_congr e
  have hd : ∑ _ : Fin 1, z.1 = z.1 := by simp
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks (fun _ : Fin 1 => z.1) hd) _).1
    (piTensor fun _ => z.rep)
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one z hd
  let χ := φ.trans ψ.symm
  obtain ⟨θ⟩ := nonempty_equiv_of_isSubquotient hi z.2.rep.irr
    (hsub.trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective))
  exact ((IrrGL.of_rep z).symm.trans ((IrrGL.of_eq_of.2 ⟨θ⟩).trans (IrrGL.of_rep ⟨_, c⟩))).symm

theorem exists_equiv_of_cell {l : ℕ} (x y : Fin l → IrrGL (k := k)) (hxc : ∀ a, (x a).IsCusp)
    (hyp : ∀ a, 0 < (y a).1) (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1)
    (h0 : jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) ≠ 0) :
    ∃ e : Fin l ≃ Fin l, ∀ a, y a = x (e a) := by
  have hG := GlobalTheory.CompanionTheory.GeoLink.geometricLemma
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible := _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun j => (y j).2.rep
  have hτs : IsSmooth (piTensor fun j => (y j).rep) := isSmooth_piTensor fun j => (y j).2.rep.smooth
  obtain ⟨s, hrow, hcol⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (hG k).2 f g (fun i => (x i).2.rep.smooth)
    (fun i => (x i).2.rep.hasFiniteLength) hτ hτs h0
  have hR : ∀ i, ∃ t : Fin l → Multiset (IrrGL (k := k)), (∀ j, HasSupport (s i j).ρ (t j)) ∧ {x i} = ∑ j, t j :=
    fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_sum_of_jac hG hBZ (hasSupport_self (hxc i)) (f i)
      (_root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun j => s i j) (hrow i)
      (fun j => s i j) (fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle _ (fun j => (s i j).irr) j)
  choose t ht hAt using hR
  have hC : ∀ j, HasSupport (y j).rep (∑ i, t i j) := by
    intro j
    have hd : ∑ i, b.1 i j = (y j).1 := by simpa using Fintype.card_congr (g j)
    have hy := GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (y j).rep) (fun j => (y j).2.rep.irr) j
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (s i j).ρ) j (y j).2.rep.irr
      (hy.trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1
      (piTensor fun i => (s i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr)
    exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr)
      (fun i => (ht i j).of_equiv (IrrGL.equivOf _ _ _)) (y j).2.rep.irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  choose r hr1 hr0 using fun i => exists_eq_singleton_of_sum' (hAt i)
  have hsurj : Function.Surjective r := by
    intro j
    by_contra hj
    push_neg at hj
    have hz : ∑ i, t i j = 0 := Finset.sum_eq_zero fun i _ => hr0 i j (Ne.symm (hj i))
    have h1 := (hC j).sum_fst
    rw [hz] at h1
    have := hyp j
    simp at h1
    omega
  have hbij : Function.Bijective r := ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  let E := Equiv.ofBijective r hbij
  refine ⟨E.symm, fun j => ?_⟩
  have hrE : r (E.symm j) = j := E.apply_symm_apply j
  have hs1 : ∑ i, t i j = {x (E.symm j)} := by
    rw [Finset.sum_eq_single (E.symm j)]
    · rw [← hr1 (E.symm j), hrE]
    · intro i _ hi
      refine hr0 i j fun e => hi ?_
      exact hbij.1 (e.symm.trans hrE.symm)
    · simp
  have h2 := hC j
  rw [hs1] at h2
  exact eq_of_hasSupport_singleton h2

theorem exists_equiv_of_jm_ne_zero {l N : ℕ} (x y : Fin l → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) (hxc : ∀ a, (x a).IsCusp) (hyp : ∀ a, 0 < (y a).1)
    (h : jm y hy (prodIrr x hx) ≠ 0) : ∃ e : Fin l ≃ Fin l, ∀ a, y a = x (e a) := by
  classical
  haveI : Fintype (SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) := Fintype.ofFinite _
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible :=
    _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k _ _ fun j => (y j).2.rep
  let f : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1 :=
    fun b => b.nonempty_rows.some
  let g : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1 :=
    fun b => b.nonempty_cols.some
  have h1 := (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1.jhMult_eq (stdBlocks (fun a => (x a).1) hx)
    (stdBlocks (fun a => (y a).1) hy) (isSmooth_piTensor fun i => (x i).2.rep.smooth) f g hτ
  have h2 : jm y hy (prodIrr x hx) = jhMult (piTensor fun j => (y j).rep)
      (GlobalTheory.SmGL.jac (stdBlocks (fun a => (y a).1) hy) (parInd (stdBlocks (fun a => (x a).1) hx)
        (piTensor fun i => (x i).rep))) := rfl
  rw [h2, h1] at h
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact exists_equiv_of_cell x y hxc hyp b (f b) (g b) hb

theorem jm_le_one (hA : IrreducibleAdmissibleGL) {l N : ℕ} (x y : Fin l → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp)
    (hinj : Function.Injective x) : jm y hy (prodIrr x hx) ≤ 1 := by
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA x y hx hy hxc hyc]
  have : Set.ncard {e : Fin l ≃ Fin l | ∀ a, y a = x (e a)} ≤ 1 := by
    refine (Set.ncard_le_one_iff (Set.toFinite _)).2 fun {e e'} he he' => Equiv.ext fun a => hinj ?_
    exact (he a).symm.trans (he' a)
  exact_mod_cast this

section Sat

variable {N : ℕ} {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y]
  [Module ℂ Y]

theorem false_of_sub_quot {h : ℕ} (t : Fin h → IrrGL (k := k)) (ht : ∑ a, (t a).1 = N) (hA : IrreducibleAdmissibleGL)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) {ω : Representation ℂ (GL (Fin N) k) W}
    (f : ω.IntertwiningMap π) (hf : Function.Injective f) {τ : Representation ℂ (GL (Fin N) k) Y}
    (q : (GlobalTheory.CompanionTheory.BZSeg.TwoSeg.quotRep π ω f).IntertwiningMap τ) (hq : Function.Surjective q)
    (hle : jm t ht π ≤ 1) (h1 : 1 ≤ jm t ht ω) (h2 : 1 ≤ jm t ht τ) : False := by
  let Q := GlobalTheory.CompanionTheory.BZSeg.TwoSeg.quotRep π ω f
  let p : π.IntertwiningMap Q := ⟨(LinearMap.range f.toLinearMap).mkQ, fun g => by ext v; rfl⟩
  have hp : Function.Surjective p := Submodule.mkQ_surjective _
  have hex : Function.Exact f p := fun v => by
    show (LinearMap.range f.toLinearMap).mkQ v = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl
  have hadd : jm t ht π = jm t ht ω + jm t ht Q :=
    GlobalTheory.CompanionTheory.SocleJm.jhMult_jac_exact _ (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA t) f p hπ hf hp hex
  have hQs : IsSmooth Q := (IsSubquotient.of_surjective p hp).isSmooth hπ
  have h3 : jm t ht τ ≤ jm t ht Q :=
    GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient t ht τ Q hQs (.of_surjective q hq)
  have h4 : (1 : ℕ∞) + 1 ≤ 1 := calc
    (1 : ℕ∞) + 1 ≤ jm t ht ω + jm t ht Q := add_le_add h1 (h2.trans h3)
    _ = jm t ht π := hadd.symm
    _ ≤ 1 := hle
  exact absurd h4 (by norm_num)

theorem surjective_of_jm (hA : IrreducibleAdmissibleGL) {x y : IrrGL (k := k)} (hx : x.IsCusp) (hy : y.IsCusp) (hne : x ≠ y)
    (hd : ∑ a, (![x, y] a).1 = N) (hd' : ∑ a, (![y, x] a).1 = N) {ω : Representation ℂ (GL (Fin N) k) W}
    (f : ω.IntertwiningMap (prodIrr ![x, y] hd)) (hf : Function.Injective f)
    (h1 : 1 ≤ jm ![x, y] hd ω) (h2 : 1 ≤ jm ![y, x] hd' ω) : Function.Surjective f := by
  by_contra hns
  have hs := isSmooth_prodIrr ![x, y] hd
  have hxc : ∀ a, (![x, y] a).IsCusp := Fin.forall_fin_two.2 ⟨hx, hy⟩
  have hyc : ∀ a, (![y, x] a).IsCusp := Fin.forall_fin_two.2 ⟨hy, hx⟩
  have hinj : Function.Injective ![x, y] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hfl : HasFiniteLength (prodIrr ![x, y] hd) :=
    GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k 2 N
      (fun a => (![x, y] a).1) (fun a => GlobalTheory.SplitRead.Irr.ofIrrRep (![x, y] a).2.rep) _
  let Q := GlobalTheory.CompanionTheory.BZSeg.TwoSeg.quotRep (prodIrr ![x, y] hd) ω f
  let p : (prodIrr ![x, y] hd).IntertwiningMap Q := ⟨(LinearMap.range f.toLinearMap).mkQ, fun g => by ext v; rfl⟩
  have hp : Function.Surjective p := Submodule.mkQ_surjective _
  have hQs : IsSmooth Q := (IsSubquotient.of_surjective p hp).isSmooth hs
  have hQn : Nontrivial (_ ⧸ LinearMap.range f.toLinearMap) :=
    Submodule.Quotient.nontrivial_iff.2 fun h => hns (LinearMap.range_eq_top.1 h)
  obtain ⟨Y', _, _, τ, hτs, hτi, q, hq⟩ := IrrQuot.exists_irreducible_smooth_quotient Q hQs
    (GlobalTheory.JacquetBlocks.hasFiniteLength_of_surjective p hp hfl) hQn
  have hτsub : IsSubquotient τ (prodIrr ![x, y] hd) := (IsSubquotient.of_surjective q hq).trans (.of_surjective p hp)
  have hsum : x.1 + y.1 = N := by simpa [Fin.sum_univ_two] using hd
  have hN : 0 < N := by have := hx.1; omega
  obtain ⟨u, hu, hu0, g, hg⟩ := GlobalTheory.CompanionTheory.JacquetLeft.exists_embedding hA τ hτs hτi hN
  haveI hYn : Nontrivial Y' := GlobalTheory.JacFactor.nontrivial_of_isIrreducible hτi
  have hg0 : ∃ v, g v ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Y')
    exact ⟨v, fun h => hv (hg (h.trans (map_zero g).symm))⟩
  have hj := GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA u hu τ hτs g hg0
  have hj' := GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient u hu τ _ hs hτsub
  by_cases hz : (u 1).1 = 0
  · obtain ⟨z, hz1, ⟨E⟩⟩ := GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single u hu 0 (fun i hi => by
      obtain rfl : i = 1 := by omega
      exact hz)
    have hsq : IsSubquotient τ z.rep.ρ :=
      .of_injective (E.toIntertwiningMap.comp g) (E.toLinearEquiv.injective.comp hg)
    obtain ⟨θ⟩ := nonempty_equiv_of_isSubquotient hτi z.rep.irr hsq
    have hc : IrrGL.IsCusp (⟨N, z⟩ : IrrGL (k := k)) := hz1 ▸ hu0
    have h0 := GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp hA ⟨N, z⟩ ![x, y] hd hc le_rfl
      (Fin.forall_fin_two.2 ⟨hx.1, hy.1⟩)
    exact jhMult_ne_zero_iff.2 ((IsSubquotient.of_injective θ.toIntertwiningMap θ.toLinearEquiv.injective).trans hτsub) h0
  · have hpos : ∀ a, 0 < (u a).1 := by
      refine Fin.forall_fin_two.2 ⟨hu0.1, Nat.pos_of_ne_zero hz⟩
    obtain ⟨e, he⟩ := exists_equiv_of_jm_ne_zero ![x, y] u hd hu hxc hpos
      (ENat.one_le_iff_ne_zero.1 (hj.trans hj'))
    have hcases : u = ![x, y] ∨ u = ![y, x] := by
      have hee : e 0 ≠ e 1 := fun h => by simpa using e.injective h
      have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
      rcases key _ _ hee with ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inl (funext (Fin.forall_fin_two.2 ⟨(he 0).trans (by simp [a]), (he 1).trans (by simp [b])⟩))
      · exact Or.inr (funext (Fin.forall_fin_two.2 ⟨(he 0).trans (by simp [a]), (he 1).trans (by simp [b])⟩))
    rcases hcases with rfl | rfl
    · exact false_of_sub_quot ![x, y] hd hA hs f hf q hq (jm_le_one hA _ _ hd hd hxc hxc hinj) h1 hj
    · exact false_of_sub_quot ![y, x] hd' hA hs f hf q hq (jm_le_one hA _ _ hd hd' hxc hyc hinj) h2 hj

end Sat

theorem nu_one_ne {x : IrrGL (k := k)} (hx : 0 < x.1) : x.nu 1 ≠ x := fun h => by
  have h1 : x.nu ((1 : ℕ) : ℂ) = x.nu ((0 : ℕ) : ℂ) := by simpa using h
  exact one_ne_zero (IrrGL.nu_natCast_inj hx |>.1 h1)

end GlobalTheory.CompanionTheory.CuspPairSub
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalMemUnitary
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG

theorem hw_harm {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam)
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V) (hc : IsCoreMod (infOf lam) E1 E2 σ A)
    (ν : Fin n → ℤ) (v : V) (hv : v ≠ 0) (hh : v ∈ hwSp E1 E2 (wtR ν)) (hdom : DomLE (wtR ν) (m0 lam)) :
    ν ∈ harmZ lam := by
  obtain ⟨S, hfd, hvS, -, hKS, -⟩ := hc.der.2 v
  have hGl : Formalism.REAL.GlRel (kF E1 E2) := GlobalTheory.CompanionTheory.RealCount.KHw.glRel_kF hc.pair
  have hK : Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) (wtR ν) v := hh
  have hanti : Antitone (wtR ν) := GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable V (kF E1 E2) S (wtR ν) v hGl hfd hKS hvS hv hK
  have hanti' : Antitone ν := fun a b hab => by
    have := hanti hab
    simpa [wtR] using this
  obtain ⟨ι, i1, i2, c, hcl, hconds⟩ := _root_.GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan n
  obtain ⟨w, hw, x, hx, hxh⟩ := hconds V (kF E1 E2) S ν v hGl hc.pair.unitK hfd hKS hvS hv hK
  have hn := _root_.GlobalTheory.CompanionTheory.DiracK.dirac_ineq lam V E1 E2 σ A hc ι c hcl _ x hx hxh
  exact GlobalTheory.T.harmonic_of_norm_bound lam hl ν hanti' hdom w hw hn

theorem hw_stable' {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} {A : V →ₗ[ℂ] V} (hA2 : A * A = 1) (hAE : ∀ a b, A * E1 a b = E2 a b * A)
    (μ : Fin n → ℝ) : ∀ x ∈ hwSp E1 E2 μ, A x ∈ hwSp E1 E2 μ := by
  have hk : ∀ a b (y : V), A (kF E1 E2 a b y) = kF E1 E2 a b (A y) := by
    intro a b y
    have h1 : A (E1 a b y) = E2 a b (A y) := LinearMap.congr_fun (hAE a b) y
    have h2 : A (E2 a b y) = E1 a b (A y) := by
      have h3 : A (E1 a b (A y)) = E2 a b (A (A y)) := LinearMap.congr_fun (hAE a b) (A y)
      have h4 : ∀ u : V, A (A u) = u := fun u => LinearMap.congr_fun hA2 u
      rw [h4] at h3
      rw [← h3, h4]
    simp only [kF, LinearMap.add_apply, map_add (f := _), h1, h2]
    abel
  intro x hx
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [← hk, hx.1 a, map_smul]
  · rw [← hk, hx.2 a b hab he, map_zero]

theorem flip_stable' {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {A : V →ₗ[ℂ] V} (hAσ : ∀ k, A * σ k = σ k * A)
    (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T) :
    ∀ t ∈ invA σ E, flipA E A T t ∈ invA σ E := by
  intro t ht k ξ
  have h1 : dualT E T (ξ ∘L E.ρ k⁻¹) = (dualT E T ξ) ∘L E.ρ k⁻¹ := by
    ext y
    have h2 := congrArg (fun S : E.V →L[ℂ] E.V => ξ (S y)) (hT k⁻¹)
    simp only [dualT, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
    exact (h2.symm)
  have h3 : flipA E A T t (ξ ∘L E.ρ k⁻¹) = A (t (dualT E T (ξ ∘L E.ρ k⁻¹))) := rfl
  have h4 : flipA E A T t ξ = A (t (dualT E T ξ)) := rfl
  rw [h3, h4, h1, ht k (dualT E T ξ)]
  exact LinearMap.congr_fun (hAσ k) _

theorem dual_stable' {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T)
    (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G) (μ : Fin n → ℝ) :
    ∀ ξ ∈ hwOf G μ, (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) ξ ∈ hwOf G μ := by
  intro ξ hξ
  have hc := _root_.GlobalTheory.CompanionTheory.RealCountG.DualComm.dualT_G E T hT G hG
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · show G a a (dualT E T ξ) = _
    rw [← hc, hξ.1 a, map_smul]
    rfl
  · show G a b (dualT E T ξ) = 0
    rw [← hc, hξ.2 a b hab he, map_zero]

theorem diagonal_mem_unitary {n : ℕ} (z : Fin n → ℂ) (hz : ∀ a, ‖z a‖ = 1) :
    (diagonal z : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  refine congrArg Matrix.diagonal (funext fun a => ?_)
  change z a * (starRingEnd ℂ) (z a) = 1
  rw [Complex.mul_conj', hz a]
  simp

theorem dualtr {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : IsLefK lam E T)
    (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G) :
    ∀ μ ∈ harmZ lam, trOn (hwOf G (wtR μ)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = 2 ^ n := by
  obtain ⟨F, hF, -, hch⟩ := _root_.GlobalTheory.CompanionTheory.RealCountG.CharDec.main E T hT.1 G hG
  intro μ hμ
  refine (_root_.GlobalTheory.CompanionTheory.CoefId.coef_harm lam hl F hF (fun ν => trOn (hwOf G (wtR ν)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)))
    (fun z hz hinj => ?_) μ hμ).2
  have hzi : Function.Injective z := fun a b h => hinj (by simp only [h])
  have h1 := hch ⟨diagonal z, diagonal_mem_unitary z hz⟩ z rfl hzi
  have h2 := GlobalTheory.T.twisted_trace_weyl_character lam E T hT ⟨diagonal z, diagonal_mem_unitary z hz⟩ z rfl hinj
  rw [← h1, h2]

theorem countG : CountG := by
  intro n lam hlam E T hT V _ _ E1 E2 σ A hc hfin
  obtain ⟨hsp, htop⟩ := _root_.GlobalTheory.CompanionTheory.RealCountG.TopeG.topeG lam hlam E T hT
  obtain ⟨G, hG⟩ := _root_.GlobalTheory.CompanionTheory.RealCountG.dualFam_exists E
  have hint := _root_.GlobalTheory.CompanionTheory.RealCountG.Intertw.intertwines V σ (kF E1 E2) hc.der E G hG
  have hmaps : ∀ t ∈ invA σ E, ∀ (μ : Fin n → ℝ), ∀ ξ ∈ hwOf G μ, t ξ ∈ hwSp E1 E2 μ := by
    intro t ht μ ξ hξ
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← hint t ht, hξ.1 a, map_smul]
    · rw [← hint t ht, hξ.2 a b hab he, map_zero]
  have hinj := _root_.GlobalTheory.CompanionTheory.RealCountG.InjG.eq_zero_of_hw V E1 E2 σ hc.pair hc.der E G hG hsp (harmZ lam)
    (fun ν v hv hh hw => hw_harm lam hlam V E1 E2 σ A hc ν v hv hh (htop ν hw))
  have hext := _root_.GlobalTheory.CompanionTheory.RealCountG.ExtMulti.exists_inv_multi V E1 E2 σ hc.pair hc.der E G hG (harmZ lam)
  have hA : ∀ μ, ∀ x ∈ hwSp E1 E2 μ, A x ∈ hwSp E1 E2 μ := hw_stable' hc.Asq hc.AE
  have hF : ∀ t ∈ invA σ E, flipA E A T t ∈ invA σ E := flip_stable' hc.Aσ E T hT.1
  have hB := dual_stable' E T hT.1 G hG
  have htr := dualtr lam hlam E T hT G hG
  let ι := {μ // μ ∈ harmZ lam}
  let W : ι → Type := fun i => hwOf G (wtR i.1)
  let H : ι → Type := fun i => hwSp E1 E2 (wtR i.1)
  let b : ∀ i, W i →ₗ[ℂ] W i := fun i =>
    (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)).restrict (p := hwOf G (wtR i.1)) (q := hwOf G (wtR i.1)) (hB _)
  let a : ∀ i, H i →ₗ[ℂ] H i := fun i => A.restrict (p := hwSp E1 E2 (wtR i.1)) (q := hwSp E1 E2 (wtR i.1)) (hA _)
  have e3 : ∀ i : ι, LinearMap.trace ℂ (W i) (b i) = 2 ^ n := by
    intro i
    have := htr i.1 i.2
    unfold trOn at this
    rwa [dite_eq_left (hB _)] at this
  haveI hWnt : ∀ i, Nontrivial (W i) := by
    intro i
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h0 : b i = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
    have := e3 i
    rw [h0, map_zero] at this
    exact (pow_ne_zero n (two_ne_zero : (2 : ℂ) ≠ 0)) this.symm
  let R0 : invA σ E →ₗ[ℂ] (∀ i, W i →ₗ[ℂ] H i) :=
    { toFun := fun t i => LinearMap.codRestrict (hwSp E1 E2 (wtR i.1)) (t.1 ∘ₗ (hwOf G (wtR i.1)).subtype)
        (fun ξ => hmaps t.1 t.2 _ ξ.1 ξ.2)
      map_add' := fun x y => by funext i; ext ξ; rfl
      map_smul' := fun c x => by funext i; ext ξ; rfl }
  have hR0 : ∀ (t : invA σ E) (i : ι) (ξ : W i), ((R0 t i ξ : hwSp E1 E2 (wtR i.1)) : V) = t.1 ξ.1 := fun _ _ _ => rfl
  have hbij : Function.Bijective R0 := by
    constructor
    · refine (injective_iff_map_eq_zero R0).2 fun t ht => ?_
      refine Subtype.ext (hinj t.1 t.2 fun μ hμ ξ hξ => ?_)
      have := hR0 t ⟨μ, hμ⟩ ⟨ξ, hξ⟩
      rw [ht] at this
      simpa using this.symm
    · intro f
      obtain ⟨t, ht, hf⟩ := hext (fun μ => if h : μ ∈ harmZ lam then f ⟨μ, h⟩ else 0)
      refine ⟨⟨t, ht⟩, ?_⟩
      funext i
      ext ξ
      rw [hR0]
      have := hf i.1 i.2 ξ
      rw [dite_eq_left i.2] at this
      exact this
  let R := LinearEquiv.ofBijective R0 hbij
  let Fl := (flipA E A T).restrict (p := invA σ E) (q := invA σ E) hF
  have hcomp : ∀ x i, R (Fl x) i = a i ∘ₗ R x i ∘ₗ b i := by
    intro x i
    ext ξ
    rfl
  haveI : FiniteDimensional ℂ (invA σ E) := hfin
  obtain ⟨hfd, htrace⟩ := _root_.GlobalTheory.CompanionTheory.HomTrace.trace_of_block_sandwich ι (invA σ E) W H R Fl a b hcomp
  have hse : harmSet lam = (harmZ lam).image wtR := harmSet_eq lam
  refine ⟨fun μ hμ => ?_, fun hne => ?_, ?_⟩
  · rw [hse, Finset.mem_image] at hμ
    obtain ⟨ν, hν, rfl⟩ := hμ
    exact ⟨hA _, hfd ⟨ν, hν⟩⟩
  · by_contra hno
    push_neg at hno
    apply hne
    refine (Submodule.eq_bot_iff _).2 fun t ht => hinj t ht fun μ hμ ξ hξ => ?_
    have h1 := hmaps t ht _ ξ hξ
    have hμ' : wtR μ ∈ harmSet lam := by
      rw [hse]
      exact Finset.mem_image_of_mem _ hμ
    rw [hno _ hμ'] at h1
    simpa using h1
  · have e1 : trOn (invA σ E) (flipA E A T) = LinearMap.trace ℂ (invA σ E) Fl := by
      unfold trOn; rw [dite_eq_left hF]
    have e2 : ∀ i : ι, trOn (hwSp E1 E2 (wtR i.1)) A = LinearMap.trace ℂ (H i) (a i) := by
      intro i
      unfold trOn; rw [dite_eq_left (hA _)]
    rw [e1, htrace, hse, Finset.sum_image (fun x _ y _ h => wtR_injective h), Finset.mul_sum,
      ← Finset.sum_coe_sort (harmZ lam)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e3 i, e2 i]

end GlobalTheory.CompanionTheory.RealCountG
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolValueAtFinsetSum
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IwaAd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

theorem holValueAt_finset_sum {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} {c : ι → ℂ} {s₀ : ℂ}
    (a : ∀ i ∈ T, HolValueAt (f i) s₀ (c i)) :
    HolValueAt (fun z => ∑ i ∈ T, f i z) s₀ (∑ i ∈ T, c i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert i T hi ih =>
    have h := (a i (Finset.mem_insert_self i T)).add
      (ih fun j hj => a j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using h

end GlobalTheory.CompanionTheory.IwaAd

end
end

