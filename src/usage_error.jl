"""
    UsageError(msg)

A problem in how Corset was called or configured: a bad option, setting or opt-out comment, or a
missing tool. The `corset` command exits with 2 on it; any other exception is Corset's own failure.
"""
struct UsageError <: Exception
    msg::String
end

Base.showerror(io::IO, error_::UsageError)::Nothing = print(io, error_.msg)
