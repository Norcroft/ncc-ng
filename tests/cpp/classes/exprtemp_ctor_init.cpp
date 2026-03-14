// Constructor initialisers that force optimise0() to create temporaries
// outside an explicit exprtemp scope.

struct Matrix {
    int value;

    Matrix() {}

    static Matrix identity() {
        return Matrix();
    }
};

struct State {
    Matrix initial;

    State() : initial(Matrix::identity()) {}
};

State make_state() {
    return State();
}
