program main
    !use ifport
    implicit none

    integer(4) :: i, seed
    real(8) :: seed1

    call random_seed()

    do i = 1, 10
        call random_number(seed1)
        seed =  int(seed1*10D7)
        write(*,*) i
        write(*,*)"seed = ", seed
        call test(seed)
        write(*,*)
    enddo

end program main
